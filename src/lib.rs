use std::{
    fmt::{self, Display},
    iter::Peekable,
    slice::Iter,
};

#[derive(Debug, PartialEq)]
pub enum JsonValue {
    Object(Vec<(String, JsonValue)>),
    Array(Vec<JsonValue>),
    String(String),
    Int(i64),
    Float(f64),
    Bool(bool),
    Null,
}

#[derive(Debug)]
pub enum ParsingError {
    UnexpectedToken(Box<str>),
    StackOverflow,
    InvalidLiteral(Box<str>),
    InvalidNumber(Box<str>),
    InvalidBoolean(Box<str>),
    InvalidString(Box<str>),
    InvalidArray(Box<str>),
    InvalidObject(Box<str>),
}

impl Display for ParsingError {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Self::InvalidArray(x) => write!(f, "Invalid array {}", x),
            Self::InvalidLiteral(x) => write!(f, "Invalid Literal {}", x),
            Self::InvalidNumber(x) => write!(f, "Invalid number {}", x),
            Self::InvalidBoolean(x) => write!(f, "Invalid boolean {}", x),
            Self::InvalidString(x) => write!(f, "Invalid string {}", x),
            Self::InvalidObject(x) => write!(f, "Invalid Object {}", x),
            Self::UnexpectedToken(x) => write!(f, "Unexpected token: {}", x),
            Self::StackOverflow => write!(f, "Maximum stack depth reached"),
        }
    }
}

type ParsingResult<T> = Result<T, ParsingError>;

impl Display for JsonValue {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Self::Null => write!(f, "null"),
            Self::Bool(b) => write!(f, "{}", b),
            Self::Int(i) => write!(f, "{}", i),
            Self::Float(v) => write!(f, "{}", v),
            Self::String(s) => write!(f, "\"{}\"", s),
            Self::Array(arr) => {
                write!(f, "[")?;
                for (i, item) in arr.iter().enumerate() {
                    if i > 0 {
                        write!(f, ", ")?;
                    }
                    write!(f, "{}", item)?;
                }
                write!(f, "]")
            }
            Self::Object(obj) => {
                write!(f, "{{")?;
                for (i, (key, value)) in obj.iter().enumerate() {
                    if i > 0 {
                        write!(f, ", ")?;
                    }
                    write!(f, "\"{}\": {}", key, value)?;
                }
                write!(f, "}}")
            }
        }
    }
}

#[derive(Debug, PartialEq)]
pub enum Token {
    RBrace,
    LBrace,
    Integer(i64),
    Float(f64),
    Boolean(bool),
    Null,
    Colon,
    Comma,
    LBracket,
    RBracket,
    String(String),
}

fn parse_string(chars: &mut std::iter::Peekable<std::str::Chars>) -> Result<String, String> {
    let mut value = String::new();

    while let Some(c) = chars.next() {
        match c {
            '"' => return Ok(value),
            '\\' => {
                match chars.next() {
                    Some('"') => value.push('"'),
                    Some('\\') => value.push('\\'),
                    Some('/') => value.push('/'),
                    Some('b') => value.push('\u{0008}'),
                    Some('f') => value.push('\u{000C}'),
                    Some('n') => value.push('\n'),
                    Some('r') => value.push('\r'),
                    Some('t') => value.push('\t'),
                    Some('u') => {
                        // Parse \uXXXX Unicode escape
                        match parse_unicode_escape(chars) {
                            Ok(ch) => value.push(ch),
                            Err(msg) => return Err(msg),
                        }
                    }
                    Some(c) => return Err(format!("Invalid escape sequence \\{}", c)),
                    None => {
                        return Err("Unexpected end of string during escape sequence".to_string());
                    }
                }
            }
            c if c.is_control() => {
                return Err(format!(
                    "Unescaped control character U+{:04X} in string",
                    c as u32
                ));
            }
            c => value.push(c),
        }
    }

    Err("Unterminated string".to_string())
}

fn parse_unicode_escape(chars: &mut std::iter::Peekable<std::str::Chars>) -> Result<char, String> {
    let mut hex_digits = String::new();

    // Read exactly 4 hex digits
    for _ in 0..4 {
        match chars.next() {
            Some(c) if c.is_ascii_hexdigit() => hex_digits.push(c),
            Some(c) => return Err(format!("Invalid hex digit '{}' in Unicode escape", c)),
            None => return Err("Incomplete Unicode escape sequence".to_string()),
        }
    }

    // Parse hex to u32
    let code_point = u32::from_str_radix(&hex_digits, 16)
        .map_err(|_| "Invalid hex number in Unicode escape".to_string())?;

    // Handle surrogate pairs (U+D800-U+DFFF)
    if (0xD800..=0xDBFF).contains(&code_point) {
        // High surrogate - need to parse low surrogate
        parse_surrogate_pair(chars, code_point)
    } else if (0xDC00..=0xDFFF).contains(&code_point) {
        // Unpaired low surrogate
        Err(format!("Unpaired low surrogate U+{:04X}", code_point))
    } else {
        // Regular code point
        validate_code_point(code_point)
    }
}

fn parse_surrogate_pair(
    chars: &mut std::iter::Peekable<std::str::Chars>,
    high: u32,
) -> Result<char, String> {
    // Expect \uXXXX for low surrogate
    if chars.next() != Some('\\') || chars.next() != Some('u') {
        return Err(format!("Unpaired high surrogate U+{:04X}", high));
    }

    let mut hex_digits = String::new();
    for _ in 0..4 {
        match chars.next() {
            Some(c) if c.is_ascii_hexdigit() => hex_digits.push(c),
            Some(c) => return Err(format!("Invalid hex digit '{}' in low surrogate", c)),
            None => return Err("Incomplete low surrogate sequence".to_string()),
        }
    }

    let low = u32::from_str_radix(&hex_digits, 16)
        .map_err(|_| "Invalid hex number in low surrogate".to_string())?;

    if !(0xDC00..=0xDFFF).contains(&low) {
        return Err(format!("Expected low surrogate, got U+{:04X}", low));
    }

    // Combine surrogates into code point
    let code_point = 0x10000 + ((high - 0xD800) << 10) + (low - 0xDC00);
    validate_code_point(code_point)
}

fn validate_code_point(code_point: u32) -> Result<char, String> {
    match code_point {
        // Invalid code points
        0xFFFE | 0xFFFF => Err(format!("Invalid Unicode code point U+{:04X}", code_point)),
        // Non-characters in the BMP
        0xFDD0..=0xFDEF => Err(format!("Non-character code point U+{:04X}", code_point)),
        // Valid range
        _ => char::from_u32(code_point)
            .ok_or_else(|| format!("Invalid Unicode code point U+{:04X}", code_point)),
    }
}

pub fn tokenize(source: &str) -> Result<Vec<Token>, ParsingError> {
    let mut chars = source.chars().peekable();
    let mut tokens = Vec::new();

    while let Some(c) = chars.next() {
        match c {
            '{' => tokens.push(Token::LBrace),
            ',' => tokens.push(Token::Comma),
            ':' => tokens.push(Token::Colon),
            '}' => tokens.push(Token::RBrace),
            '[' => tokens.push(Token::LBracket),
            ']' => tokens.push(Token::RBracket),
            '"' => match parse_string(&mut chars) {
                Ok(value) => tokens.push(Token::String(value)),
                Err(msg) => {
                    return Err(ParsingError::InvalidString(msg.into()));
                }
            },
            c if c.is_ascii_digit() || c == '-' => {
                let mut s = String::new();
                s.push(c);

                if c == '-' {
                    match chars.peek() {
                        Some(&c) if c.is_ascii_digit() => {
                            s.push(chars.next().unwrap());
                        }
                        _ => {
                            return Err(ParsingError::InvalidNumber(
                                "Expected digit after '-'".into(),
                            ));
                        }
                    }
                } else {
                }

                let start_idx = if c == '-' { 1 } else { 0 };
                if s.chars().nth(start_idx) == Some('0') {
                    if let Some(&next) = chars.peek() {
                        if next.is_ascii_digit() {
                            return Err(ParsingError::InvalidNumber(
                                "Leading zeros not allowed".into(),
                            ));
                        }
                    }
                }

                while let Some(&c) = chars.peek() {
                    if c.is_ascii_digit() {
                        s.push(chars.next().unwrap());
                    } else {
                        break;
                    }
                }

                let mut has_fraction = false;
                if let Some(&'.') = chars.peek() {
                    s.push(chars.next().unwrap());
                    has_fraction = true;

                    match chars.peek() {
                        Some(&c) if c.is_ascii_digit() => {
                            s.push(chars.next().unwrap());
                        }
                        _ => {
                            return Err(ParsingError::InvalidNumber(
                                "Missing digit after '.'".into(),
                            ));
                        }
                    }

                    while let Some(&c) = chars.peek() {
                        if c.is_ascii_digit() {
                            s.push(chars.next().unwrap());
                        } else {
                            break;
                        }
                    }
                }

                let mut has_exponent = false;
                if let Some(&('e' | 'E')) = chars.peek() {
                    s.push(chars.next().unwrap());
                    has_exponent = true;

                    if let Some(&('+' | '-')) = chars.peek() {
                        s.push(chars.next().unwrap());
                    }

                    match chars.peek() {
                        Some(&c) if c.is_ascii_digit() => {
                            s.push(chars.next().unwrap());
                        }
                        _ => {
                            return Err(ParsingError::InvalidNumber(
                                "Exponent must have digits".into(),
                            ));
                        }
                    }

                    while let Some(&c) = chars.peek() {
                        if c.is_ascii_digit() {
                            s.push(chars.next().unwrap());
                        } else {
                            break;
                        }
                    }
                }

                let number = if has_fraction || has_exponent {
                    s.parse::<f64>()
                        .map(Token::Float)
                        .map_err(|_| ParsingError::InvalidNumber(s.into()))?
                } else {
                    s.parse::<i64>()
                        .map(Token::Integer)
                        .map_err(|_| ParsingError::InvalidNumber(s.into()))?
                };
                tokens.push(number);
            }
            c if c.is_ascii_alphabetic() => {
                let mut literal = String::new();
                literal.push(c);

                while let Some(&next) = chars.peek() {
                    if next.is_ascii_alphanumeric() {
                        literal.push(chars.next().unwrap());
                    } else {
                        break;
                    }
                }

                match literal.as_str() {
                    "true" => tokens.push(Token::Boolean(true)),
                    "false" => tokens.push(Token::Boolean(false)),
                    "null" => tokens.push(Token::Null),
                    x => {
                        return Err(ParsingError::InvalidLiteral(
                            format!("{} is not a valid literal", x).into(),
                        ));
                    }
                }
            }
            ' ' | '\t' | '\n' | '\r' => {}
            x => return Err(ParsingError::UnexpectedToken(format!("Char {}", x).into())),
        }
    }
    Ok(tokens)
}

pub fn parse(source: &str) -> ParsingResult<JsonValue> {
    match tokenize(source) {
        Ok(tokens) => {
            let mut tokens = tokens.iter().peekable();
            let value = parse_value(&mut tokens, 0)?;

            if tokens.peek().is_some() {
                return Err(ParsingError::UnexpectedToken(
                    "Extra tokens after complete JSON value".into(),
                ));
            }

            Ok(value)
        }
        Err(error) => Err(error),
    }
}
const MAX_NESTING_DEPTH: usize = 1000;
pub fn parse_value(
    tokens: &mut Peekable<Iter<'_, Token>>,
    depth: usize,
) -> ParsingResult<JsonValue> {
    if depth > MAX_NESTING_DEPTH {
        return Err(ParsingError::StackOverflow);
    }
    match tokens.peek() {
        Some(Token::Float(v)) => {
            // TODO: Fix this hack
            let v = *v;
            tokens.next();
            Ok(JsonValue::Float(v))
        }
        Some(Token::Null) => {
            tokens.next();
            Ok(JsonValue::Null)
        }
        Some(Token::Boolean(b)) => {
            tokens.next();
            Ok(JsonValue::Bool(*b))
        }
        Some(Token::Integer(v)) => {
            let v = *v;
            tokens.next();
            Ok(JsonValue::Int(v))
        }
        Some(Token::String(ident)) => {
            tokens.next();
            Ok(JsonValue::String(ident.to_string()))
        }
        Some(Token::LBracket) => {
            let mut members = Vec::new();
            tokens.next();

            if let Some(Token::RBracket) = tokens.peek() {
                tokens.next();
                return Ok(JsonValue::Array(members));
            }

            loop {
                let value = parse_value(tokens, depth + 1)?;
                members.push(value);

                match tokens.peek() {
                    Some(Token::Comma) => {
                        tokens.next();
                        if let Some(Token::RBracket) = tokens.peek() {
                            return Err(ParsingError::UnexpectedToken(
                                "Trailing comma in array".into(),
                            ));
                        }
                    }
                    Some(Token::RBracket) => {
                        tokens.next();
                        break;
                    }
                    other => {
                        return Err(ParsingError::UnexpectedToken(
                            format!("Expected comma or closing bracket, found {:?}", other).into(),
                        ));
                    }
                }
            }
            Ok(JsonValue::Array(members))
        }
        Some(Token::LBrace) => {
            let mut members = Vec::new();
            tokens.next(); // consume LBrace

            // Handle empty object
            if let Some(Token::RBrace) = tokens.peek() {
                tokens.next();
                return Ok(JsonValue::Object(members));
            }

            loop {
                let key_token = tokens.next();
                let Some(Token::String(key)) = key_token else {
                    return Err(ParsingError::UnexpectedToken("Expected object key".into()));
                };

                if tokens.next() != Some(&Token::Colon) {
                    return Err(ParsingError::UnexpectedToken(
                        "Expected colon after object key".into(),
                    ));
                }

                let value = parse_value(tokens, depth + 1)?;
                members.push((key.clone(), value));

                match tokens.peek() {
                    Some(Token::Comma) => {
                        tokens.next(); // consume comma
                        // Check for trailing comma
                        if let Some(Token::RBrace) = tokens.peek() {
                            return Err(ParsingError::UnexpectedToken(
                                "Trailing comma in object".into(),
                            ));
                        }
                    }
                    Some(Token::RBrace) => {
                        tokens.next(); // consume RBrace
                        break;
                    }
                    other => {
                        return Err(ParsingError::UnexpectedToken(
                            format!("Expected comma or closing brace, found {:?}", other).into(),
                        ));
                    }
                }
            }
            Ok(JsonValue::Object(members))
        }
        x => Err(ParsingError::UnexpectedToken(
            format!("Invalid token {:?}", x).into(),
        )),
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    #[test]
    fn lex_null() {
        let result = parse("null");
        assert!(result.is_ok())
    }
    #[test]
    fn parse_numbers() {
        let result = parse("12345");
        assert_eq!(result.unwrap(), JsonValue::Int(12345));
        let result = parse("1.234");
        assert_eq!(result.unwrap(), JsonValue::Float(1.234));
    }

    #[test]
    fn nested_arrays() {
        let result = parse(
            "[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]",
        );

        assert!(result.is_ok())
    }

    #[test]
    fn i_string_iso_latin_1() {
        let result = parse(r#"["E9"]"#);
        assert!(result.is_ok())
    }

    #[test]
    fn test_y_array_arrays_with_spaces() {
        let result = parse("[[]   ]");
        assert!(result.is_ok())
    }

    #[test]
    fn test_y_array_empty_string() {
        let result = parse("[\"\"]");
        assert!(result.is_ok());
    }

    #[test]
    fn test_y_array_empty() {
        let result = parse("[]");
        assert!(result.is_ok());
    }

    #[test]
    fn test_y_array_ending_with_newline() {
        let result = parse("[\"a\"]");
        assert!(result.is_ok());
    }

    #[test]
    fn test_y_array_false() {
        let result = parse("[false]");
        assert!(result.is_ok());
    }

    #[test]
    fn test_y_array_heterogeneous() {
        let result = parse("[null, 1, \"1\", {}]");
        assert!(result.is_ok());
    }

    #[test]
    fn test_y_array_null() {
        let result = parse("[null]");
        assert!(result.is_ok());
    }

    #[test]
    fn test_y_array_with_1_and_newline() {
        let result = parse("[1\n]");
        assert!(result.is_ok());
    }

    #[test]
    fn test_y_array_with_leading_space() {
        let result = parse(" [1]");
        assert!(result.is_ok());
    }

    #[test]
    fn test_y_array_with_several_null() {
        let result = parse("[1,null,null,null,2]");
        assert!(result.is_ok());
    }

    #[test]
    fn test_y_array_with_trailing_space() {
        let result = parse("[2]");
        assert!(result.is_ok());
    }

    #[test]
    fn test_y_number() {
        let result = parse("[123e65]");
        assert!(result.is_ok());
    }

    #[test]
    fn test_y_number_0e_plus_1() {
        let result = parse("[0e+1]");
        dbg!(&result);
        assert!(result.is_ok());
    }

    #[test]
    fn test_y_number_0e1() {
        let result = parse("[0e1]");
        assert!(result.is_ok());
    }

    #[test]
    fn test_y_number_after_space() {
        let result = parse("[ 4]");
        assert!(result.is_ok());
    }

    #[test]
    fn test_y_number_double_close_to_zero() {
        let result = parse(
            "[-0.000000000000000000000000000000000000000000000000000000000000000000000000000001]",
        );
        assert!(result.is_ok());
    }

    #[test]
    fn test_y_object_basic() {
        let result = parse("{\"asd\":\"sdf\"}");
        assert!(result.is_ok());
    }

    #[test]
    fn test_y_string_simple_ascii() {
        let result = parse("[\"asd \"]");
        assert!(result.is_ok());
    }

    #[test]
    fn test_y_structure_lonely_null() {
        let result = parse("null");
        assert!(result.is_ok());
    }

    #[test]
    fn test_y_empty_string() {
        let result = parse(r#""[]""#);
        assert!(result.is_ok());
    }

    // Test functions for invalid JSON files (n_* files) - should fail parsing

    // ARRAY TESTS - Invalid arrays
    #[test]
    fn test_n_array_1_true_without_comma() {
        let result = parse("[1 true]");
        assert!(result.is_err());
    }

    #[test]
    fn test_n_array_a_invalid_utf8() {
        let result = parse("[aÿ]");
        assert!(result.is_err());
    }

    #[test]
    fn test_n_array_colon_instead_of_comma() {
        let result = parse("[1:2]");
        assert!(result.is_err());
    }

    #[test]
    fn test_n_array_comma_after_close() {
        let result = parse("[\"\"],");
        assert!(result.is_err());
    }

    #[test]
    fn test_n_array_comma_and_number() {
        let result = parse("[,1]");
        assert!(result.is_err());
    }

    #[test]
    fn test_n_array_double_comma() {
        let result = parse("[1,,2]");
        assert!(result.is_err());
    }

    #[test]
    fn test_n_array_double_extra_comma() {
        let result = parse("[\"x\",,]");
        assert!(result.is_err());
    }

    #[test]
    fn test_n_array_extra_close() {
        let result = parse("[\"x\"]]");
        assert!(result.is_err());
    }

    #[test]
    fn test_n_array_extra_comma() {
        let result = parse("[\"\",]");
        assert!(result.is_err());
    }

    #[test]
    fn test_n_array_incomplete() {
        let result = parse("[\"x\"");
        assert!(result.is_err());
    }

    #[test]
    fn test_n_array_incomplete_invalid_value() {
        let result = parse("[x");
        assert!(result.is_err());
    }

    #[test]
    fn test_n_array_inner_array_no_comma() {
        let result = parse("[3[4]]");
        assert!(result.is_err());
    }

    #[test]
    fn test_n_array_invalid_utf8() {
        let result = parse("[ÿ]");
        assert!(result.is_err());
    }

    #[test]
    fn test_n_array_items_separated_by_semicolon() {
        let result = parse("[1;2]");
        assert!(result.is_err());
    }

    #[test]
    fn test_n_array_just_comma() {
        let result = parse("[,]");
        assert!(result.is_err());
    }

    #[test]
    fn test_n_array_just_minus() {
        let result = parse("[-]");
        assert!(result.is_err());
    }

    #[test]
    fn test_n_array_missing_value() {
        let result = parse("[   , \"\"]");
        assert!(result.is_err());
    }

    #[test]
    fn test_n_array_newlines_unclosed() {
        let result = parse("[\"a\",\n4\n,1,");
        assert!(result.is_err());
    }

    #[test]
    fn test_n_array_number_and_comma() {
        let result = parse("[1,]");
        assert!(result.is_err());
    }

    #[test]
    fn test_n_array_number_and_several_commas() {
        let result = parse("[1,,]");
        assert!(result.is_err());
    }

    #[test]
    fn test_n_array_spaces_vertical_tab_formfeed() {
        let result = parse("[\"\u{000B}\"]");
        assert!(result.is_err());
    }

    #[test]
    fn test_n_array_star_inside() {
        let result = parse("[*]");
        assert!(result.is_err());
    }

    #[test]
    fn test_n_array_unclosed() {
        let result = parse("[\"\"");
        assert!(result.is_err());
    }

    #[test]
    fn test_n_array_unclosed_trailing_comma() {
        let result = parse("[1,");
        assert!(result.is_err());
    }

    #[test]
    fn test_n_array_unclosed_with_new_lines() {
        let result = parse("[1,\n1\n,1");
        assert!(result.is_err());
    }

    #[test]
    fn test_n_array_unclosed_with_object_inside() {
        let result = parse("[{}");
        assert!(result.is_err());
    }

    // INCOMPLETE TESTS
    #[test]
    fn test_n_incomplete_false() {
        let result = parse("fals");
        assert!(result.is_err());
    }

    #[test]
    fn test_n_incomplete_null() {
        let result = parse("nul");
        assert!(result.is_err());
    }

    #[test]
    fn test_n_incomplete_true() {
        let result = parse("tru");
        assert!(result.is_err());
    }

    // NUMBER TESTS - Invalid numbers
    #[test]
    fn test_n_number_plus_plus() {
        let result = parse("[++1234]");
        assert!(result.is_err());
    }

    #[test]
    fn test_n_number_plus_1() {
        let result = parse("[+1]");
        assert!(result.is_err());
    }

    #[test]
    fn test_n_number_plus_inf() {
        let result = parse("[+Inf]");
        assert!(result.is_err());
    }

    #[test]
    fn test_n_number_minus_01() {
        let result = parse("[- 1]");
        assert!(result.is_err());
    }

    #[test]
    fn test_n_number_minus_1_0_dot_dot() {
        let result = parse("[-1.0..]");
        assert!(result.is_err());
    }

    #[test]
    fn test_n_number_minus_2_dot_dot() {
        let result = parse("[-2..]");
        assert!(result.is_err());
    }

    #[test]
    fn test_n_number_minus_nan() {
        let result = parse("[-NaN]");
        assert!(result.is_err());
    }

    #[test]
    fn test_n_number_dot_minus_1() {
        let result = parse("[.-1]");
        assert!(result.is_err());
    }

    #[test]
    fn test_n_number_dot_2e_minus_3() {
        let result = parse("[.2e-3]");
        assert!(result.is_err());
    }

    #[test]
    fn test_n_number_0_1_2() {
        let result = parse("[0.1.2]");
        assert!(result.is_err());
    }

    #[test]
    fn test_n_number_0_3e_plus() {
        let result = parse("[0.3e+]");
        assert!(result.is_err());
    }

    #[test]
    fn test_n_number_0_3e() {
        let result = parse("[0.3e]");
        assert!(result.is_err());
    }

    #[test]
    fn test_n_number_0_e1() {
        let result = parse("[0.e1]");
        dbg!(&result);
        assert!(result.is_err());
    }

    #[test]
    fn test_n_number_0_capital_e_plus() {
        let result = parse("[0E+]");
        assert!(result.is_err());
    }

    #[test]
    fn test_n_number_0_capital_e() {
        let result = parse("[0E]");
        assert!(result.is_err());
    }

    #[test]
    fn test_n_number_0e_plus() {
        let result = parse("[0e+]");
        assert!(result.is_err());
    }

    #[test]
    fn test_n_number_0e() {
        let result = parse("[0e]");
        assert!(result.is_err());
    }

    #[test]
    fn test_n_number_1_0e_plus() {
        let result = parse("[1.0e+]");
        assert!(result.is_err());
    }

    #[test]
    fn test_n_number_1_0e_minus() {
        let result = parse("[1.0e-]");
        assert!(result.is_err());
    }

    #[test]
    fn test_n_number_1_0e() {
        let result = parse("[1.0e]");
        assert!(result.is_err());
    }

    #[test]
    fn test_n_number_1_000() {
        let result = parse("[1 000.0]");
        assert!(result.is_err());
    }

    #[test]
    fn test_n_number_1ee2() {
        let result = parse("[1eE2]");
        assert!(result.is_err());
    }

    #[test]
    fn test_n_number_2_e_plus_3() {
        let result = parse("[2.e+3]");
        assert!(result.is_err());
    }

    #[test]
    fn test_n_number_2_e_minus_3() {
        let result = parse("[2.e-3]");
        dbg!(&result);
        assert!(result.is_err());
    }

    #[test]
    fn test_n_number_2_e3() {
        let result = parse("[2.e3]");
        assert!(result.is_err());
    }

    #[test]
    fn test_n_number_9_e_plus() {
        let result = parse("[9.e+]");
        assert!(result.is_err());
    }

    #[test]
    fn test_n_number_inf() {
        let result = parse("[Inf]");
        assert!(result.is_err());
    }

    #[test]
    fn test_n_number_nan() {
        let result = parse("[NaN]");
        assert!(result.is_err());
    }

    #[test]
    fn test_n_number_expression() {
        let result = parse("[1+2]");
        assert!(result.is_err());
    }

    #[test]
    fn test_n_number_hex_1_digit() {
        let result = parse("[0x1]");
        assert!(result.is_err());
    }

    #[test]
    fn test_n_number_hex_2_digits() {
        let result = parse("[0x42]");
        assert!(result.is_err());
    }

    #[test]
    fn test_n_number_infinity() {
        let result = parse("[Infinity]");
        assert!(result.is_err());
    }

    #[test]
    fn test_n_number_invalid_plus_minus() {
        let result = parse("[0e+-1]");
        assert!(result.is_err());
    }

    #[test]
    fn test_n_number_invalid_negative_real() {
        let result = parse("[-123.123foo]");
        assert!(result.is_err());
    }

    #[test]
    fn test_n_number_minus_infinity() {
        let result = parse("[-Infinity]");
        assert!(result.is_err());
    }

    #[test]
    fn test_n_number_minus_sign_with_trailing_garbage() {
        let result = parse("[-foo]");
        assert!(result.is_err());
    }

    #[test]
    fn test_n_number_minus_space_1() {
        let result = parse("[- 1]");
        assert!(result.is_err());
    }

    #[test]
    fn test_n_number_neg_int_starting_with_zero() {
        let result = parse("[-012]");
        assert!(result.is_err());
    }

    #[test]
    fn test_n_number_neg_real_without_int_part() {
        let result = parse("[-.123]");
        assert!(result.is_err());
    }

    #[test]
    fn test_n_number_neg_with_garbage_at_end() {
        let result = parse("[-1x]");
        assert!(result.is_err());
    }

    #[test]
    fn test_n_number_real_garbage_after_e() {
        let result = parse("[1ea]");
        assert!(result.is_err());
    }

    #[test]
    fn test_n_number_real_without_fractional_part() {
        let result = parse("[1.]");
        assert!(result.is_err());
    }

    #[test]
    fn test_n_number_starting_with_dot() {
        let result = parse("[.123]");
        assert!(result.is_err());
    }

    #[test]
    fn test_n_number_with_alpha() {
        let result = parse("[1.2a-3]");
        assert!(result.is_err());
    }

    #[test]
    fn test_n_number_with_alpha_char() {
        let result = parse("[1.8011670033376514H-308]");
        assert!(result.is_err());
    }

    #[test]
    fn test_n_number_with_leading_zero() {
        let result = parse("[012]");
        assert!(result.is_err());
    }

    // OBJECT TESTS - Invalid objects
    #[test]
    fn test_n_object_bad_value() {
        let result = parse("[\"x\", truth]");
        assert!(result.is_err());
    }

    #[test]
    fn test_n_object_bracket_key() {
        let result = parse("{[: \"x\"}");
        assert!(result.is_err());
    }

    #[test]
    fn test_n_object_comma_instead_of_colon() {
        let result = parse("{\"x\", null}");
        assert!(result.is_err());
    }

    #[test]
    fn test_n_object_double_colon() {
        let result = parse("{\"x\"::\"b\"}");
        assert!(result.is_err());
    }

    #[test]
    fn test_n_object_emoji() {
        let result = parse("{🇨🇭}");
        assert!(result.is_err());
    }

    #[test]
    fn test_n_object_garbage_at_end() {
        let result = parse("{\"a\":\"a\" 123}");
        assert!(result.is_err());
    }

    #[test]
    fn test_n_object_key_with_single_quotes() {
        let result = parse("{'a':0}");
        assert!(result.is_err());
    }

    #[test]
    fn test_n_object_missing_colon() {
        let result = parse("{\"a\" b}");
        assert!(result.is_err());
    }

    #[test]
    fn test_n_object_missing_key() {
        let result = parse("{:\"b\"}");
        assert!(result.is_err());
    }

    #[test]
    fn test_n_object_missing_semicolon() {
        let result = parse("{\"a\" b}");
        assert!(result.is_err());
    }

    #[test]
    fn test_n_object_missing_value() {
        let result = parse("{\"a\":}");
        assert!(result.is_err());
    }

    #[test]
    fn test_n_object_no_colon() {
        let result = parse("{\"a\"");
        assert!(result.is_err());
    }

    #[test]
    fn test_n_object_non_string_key() {
        let result = parse("{1:1}");
        assert!(result.is_err());
    }

    #[test]
    fn test_n_object_non_string_key_but_huge_number_instead() {
        let result = parse("{9999E9999:1}");
        assert!(result.is_err());
    }

    #[test]
    fn test_n_object_repeated_null_null() {
        let result = parse("{null:null,null:null}");
        assert!(result.is_err());
    }

    #[test]
    fn test_n_object_several_trailing_commas() {
        let result = parse("{\"id\":0,,,,,}");
        assert!(result.is_err());
    }

    #[test]
    fn test_n_object_single_quote() {
        let result = parse("{'a':0}");
        assert!(result.is_err());
    }

    #[test]
    fn test_n_object_trailing_comma() {
        let result = parse("{\"id\":0,}");
        assert!(result.is_err());
    }

    #[test]
    fn test_n_object_trailing_comment() {
        let result = parse("{\"a\":\"b\"}/**/");
        assert!(result.is_err());
    }

    #[test]
    fn test_n_object_trailing_comment_open() {
        let result = parse("{\"a\":\"b\"}/**//");
        assert!(result.is_err());
    }

    #[test]
    fn test_n_object_trailing_comment_slash_open() {
        let result = parse("{\"a\":\"b\"}//");
        assert!(result.is_err());
    }

    #[test]
    fn test_n_object_trailing_comment_slash_open_incomplete() {
        let result = parse("{\"a\":\"b\"}/");
        assert!(result.is_err());
    }

    #[test]
    fn test_n_object_two_commas_in_a_row() {
        let result = parse("{\"a\":\"b\",,\"c\":\"d\"}");
        assert!(result.is_err());
    }

    #[test]
    fn test_n_object_unquoted_key() {
        let result = parse("{a: \"b\"}");
        assert!(result.is_err());
    }

    #[test]
    fn test_n_object_unterminated_value() {
        let result = parse("{\"a\":\"a");
        assert!(result.is_err());
    }

    #[test]
    fn test_n_object_with_single_string() {
        let result = parse("{ \"foo\" : \"bar\", \"a\" }");
        assert!(result.is_err());
    }

    #[test]
    fn test_n_object_with_trailing_garbage() {
        let result = parse("{\"a\":\"b\"}#");
        assert!(result.is_err());
    }

    // SINGLE SPACE TEST
    #[test]
    fn test_n_single_space() {
        let result = parse(" ");
        assert!(result.is_err());
    }

    // STRING TESTS - Invalid strings
    #[test]
    fn test_n_string_1_surrogate_then_escape() {
        let result = parse("[\"\\uD800\\\"]");
        assert!(result.is_err());
    }

    #[test]
    fn test_n_string_1_surrogate_then_escape_u() {
        let result = parse("[\"\\uD800\\u\"]");
        assert!(result.is_err());
    }

    #[test]
    fn test_n_string_1_surrogate_then_escape_u1() {
        let result = parse("[\"\\uD800\\u1\"]");
        assert!(result.is_err());
    }

    #[test]
    fn test_n_string_1_surrogate_then_escape_u1x() {
        let result = parse("[\"\\uD800\\u1x\"]");
        assert!(result.is_err());
    }

    #[test]
    fn test_n_string_accentuated_char_no_quotes() {
        let result = parse("[é]");
        assert!(result.is_err());
    }

    #[test]
    fn test_n_string_backslash_00() {
        let result = parse("[\"\\\u{0000}\"]");
        assert!(result.is_err());
    }

    #[test]
    fn test_n_string_escape_x() {
        let result = parse("[\"\\x00\"]");
        assert!(result.is_err());
    }

    #[test]
    fn test_n_string_escaped_backslash_bad() {
        let result = parse("[\"\\\\\\\"]");
        assert!(result.is_err());
    }

    #[test]
    fn test_n_string_escaped_ctrl_char_tab() {
        let result = parse("[\"\\\t\"]");
        assert!(result.is_err());
    }

    #[test]
    fn test_n_string_escaped_emoji() {
        let result = parse("[\"\\🌀\"]");
        assert!(result.is_err());
    }

    #[test]
    fn test_n_string_incomplete_escape() {
        let result = parse("[\"\\\"]");
        assert!(result.is_err());
    }

    #[test]
    fn test_n_string_incomplete_escaped_character() {
        let result = parse("[\"\\u00A\"]");
        assert!(result.is_err());
    }

    #[test]
    fn test_n_string_incomplete_surrogate() {
        let result = parse("[\"\\uD834\\uDd\"]");
        assert!(result.is_err());
    }

    #[test]
    fn test_n_string_incomplete_surrogate_escape_invalid() {
        let result = parse("[\"\\uD800\\uD800\\x\"]");
        assert!(result.is_err());
    }

    #[test]
    fn test_n_string_invalid_backslash_esc() {
        let result = parse("[\"\\a\"]");
        assert!(result.is_err());
    }

    #[test]
    fn test_n_string_invalid_unicode_escape() {
        let result = parse("[\"\\uqqqq\"]");
        assert!(result.is_err());
    }

    #[test]
    fn test_n_string_invalid_utf8_after_escape() {
        let result = parse("[\"\\é\"]");
        assert!(result.is_err());
    }

    #[test]
    fn test_n_string_leading_uescaped_thinspace() {
        let result = parse("[\"\\u0020\"\"asd\"]");
        assert!(result.is_err());
    }

    #[test]
    fn test_n_string_no_quotes_with_bad_escape() {
        let result = parse("[\\n]");
        assert!(result.is_err());
    }

    #[test]
    fn test_n_string_single_doublequote() {
        let result = parse("\"");
        assert!(result.is_err());
    }

    #[test]
    fn test_n_string_single_quote() {
        let result = parse("['single quote']");
        assert!(result.is_err());
    }

    #[test]
    fn test_n_string_single_string_no_double_quotes() {
        let result = parse("abc");
        assert!(result.is_err());
    }

    #[test]
    fn test_n_string_start_escape_unclosed() {
        let result = parse("[\"\\");
        assert!(result.is_err());
    }

    #[test]
    fn test_n_string_unescaped_ctrl_char() {
        let result = parse("[\"\u{0014}\"]");
        assert!(result.is_err());
    }

    #[test]
    fn test_n_string_unescaped_newline() {
        let result = parse("[\"new\nline\"]");
        assert!(result.is_err());
    }

    #[test]
    fn test_n_string_unescaped_tab() {
        let result = parse("[\"\t\"]");
        assert!(result.is_err());
    }

    #[test]
    fn test_n_string_unicode_capital_u() {
        let result = parse("[\"\\UA66D\"]");
        assert!(result.is_err());
    }

    #[test]
    fn test_n_string_with_trailing_garbage() {
        let result = parse("[\"x\"]*");
        assert!(result.is_err());
    }

    // STRUCTURE TESTS - Invalid structures
    #[test]
    fn test_n_structure_angle_bracket_dot() {
        let result = parse("<.>");
        assert!(result.is_err());
    }

    #[test]
    fn test_n_structure_angle_bracket_null() {
        let result = parse("<null>");
        assert!(result.is_err());
    }

    #[test]
    fn test_n_structure_array_trailing_garbage() {
        let result = parse("[1]x");
        assert!(result.is_err());
    }

    #[test]
    fn test_n_structure_array_with_extra_array_close() {
        let result = parse("[1]]");
        assert!(result.is_err());
    }

    #[test]
    fn test_n_structure_array_with_unclosed_string() {
        let result = parse("[\"asd]");
        assert!(result.is_err())
    }

    #[test]
    fn test_n_structure_ascii_unicode_identifier() {
        let result = parse("aå");
        assert!(result.is_err());
    }

    #[test]
    fn test_n_structure_capitalized_true() {
        let result = parse("[True]");
        assert!(result.is_err());
    }

    #[test]
    fn test_n_structure_close_unopened_array() {
        let result = parse("]");
        assert!(result.is_err())
    }

    #[test]
    fn test_n_structure_comma_instead_of_closing_brace() {
        let result = parse("{\"x\": true,");
        assert!(result.is_err())
    }

    #[test]
    fn test_n_structure_double_array() {
        let result = parse("[][]");
        assert!(result.is_err())
    }

    #[test]
    fn test_n_structure_end_array() {
        let result = parse("]");
        assert!(result.is_err())
    }

    #[test]
    fn test_n_structure_lone_open_bracket() {
        let result = parse("[");
        assert!(result.is_err())
    }

    #[test]
    fn test_n_structure_no_data() {
        let result = parse("");
        assert!(result.is_err())
    }

    #[test]
    fn test_n_structure_number_with_trailing_garbage() {
        let result = parse("2@");
        assert!(result.is_err());
    }

    #[test]
    fn test_n_structure_object_followed_by_closing_object() {
        let result = parse("{}}");
        assert!(result.is_err())
    }

    #[test]
    fn test_n_structure_object_unclosed_no_value() {
        let result = parse("{\"asd\":");
        assert!(result.is_err())
    }

    #[test]
    fn test_n_structure_object_with_comment() {
        let result = parse("{\"a\":/*comment*/\"b\"}");
        assert!(result.is_err())
    }

    #[test]
    fn test_n_structure_object_with_trailing_garbage() {
        let result = parse("{\"a\": true} \"x\"");
        assert!(result.is_err())
    }

    #[test]
    fn test_n_structure_open_array_apostrophe() {
        let result = parse("['");
        assert!(result.is_err());
    }

    #[test]
    fn test_n_structure_open_array_comma() {
        let result = parse("[,");
        assert!(result.is_err())
    }

    #[test]
    fn test_n_structure_open_array_open_object() {
        let result = parse("[{");
        assert!(result.is_err())
    }

    #[test]
    fn test_n_structure_open_array_open_string() {
        let result = parse("[\"a");
        assert!(result.is_err());
    }

    #[test]
    fn test_n_structure_open_array_string() {
        let result = parse("[\"a\"");
        assert!(result.is_err())
    }

    #[test]
    fn test_n_structure_open_object() {
        let result = parse("{");
        assert!(result.is_err())
    }

    #[test]
    fn test_n_structure_open_object_close_array() {
        let result = parse("{]");
        assert!(result.is_err())
    }

    #[test]
    fn test_n_structure_open_object_comma() {
        let result = parse("{,");
        assert!(result.is_err())
    }

    #[test]
    fn test_n_structure_open_object_open_array() {
        let result = parse("{[");
        assert!(result.is_err())
    }

    #[test]
    fn test_n_structure_open_object_open_string() {
        let result = parse("{\"a");
        assert!(result.is_err());
    }

    #[test]
    fn test_n_structure_open_object_string_with_apostrophes() {
        let result = parse("{'a'");
        assert!(result.is_err());
    }

    #[test]
    fn test_n_structure_open_open() {
        let result = parse("[[");
        assert!(result.is_err());
    }

    #[test]
    fn test_n_structure_single_eacute() {
        let result = parse("é");
        assert!(result.is_err());
    }

    #[test]
    fn test_n_structure_single_star() {
        let result = parse("*");
        assert!(result.is_err());
    }

    #[test]
    fn test_n_structure_trailing_hash() {
        let result = parse("{\"a\":\"b\"}#{}");
        assert!(result.is_err());
    }

    #[test]
    fn test_n_structure_unclosed_array() {
        let result = parse("[1");
        assert!(result.is_err());
    }

    #[test]
    fn test_n_structure_unclosed_array_partial_null() {
        let result = parse("[ false, nul");
        assert!(result.is_err());
    }

    #[test]
    fn test_n_structure_unclosed_array_unfinished_false() {
        let result = parse("[ true, fals");
        assert!(result.is_err());
    }

    #[test]
    fn test_n_structure_unclosed_array_unfinished_true() {
        let result = parse("[ false, tru");
        assert!(result.is_err());
    }

    #[test]
    fn test_n_structure_unclosed_object() {
        let result = parse("{\"asd\":\"asd\"");
        assert!(result.is_err());
    }

    #[test]
    fn test_n_structure_unicode_identifier() {
        let result = parse("å");
        assert!(result.is_err());
    }

    #[test]
    fn test_n_structure_whitespace_formfeed() {
        let result = parse("[\u{000C}]");
        assert!(result.is_err());
    }

    #[test]
    fn test_n_multidigit_number_then_00() {
        let result = parse("123\u{0000}");
        assert!(result.is_err());
    }

    #[test]
    fn test_nocrash() {
        let result = parse("1e949");
        assert!(result.is_ok());
    }
}
