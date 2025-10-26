use std::fs;

fn main() -> Result<(), Box<dyn std::error::Error>> {
    println!("Generating fuzzing corpus from test_specs...");

    // Create corpus directories
    fs::create_dir_all("fuzz/corpus/parse_json")?;
    fs::create_dir_all("fuzz/corpus/tokenize_json")?;
    fs::create_dir_all("fuzz/corpus/parse_numbers")?;
    fs::create_dir_all("fuzz/corpus/parse_strings")?;
    fs::create_dir_all("corpus/valid")?;
    fs::create_dir_all("corpus/invalid")?;
    fs::create_dir_all("corpus/implementation_defined")?;

    let test_specs_dir = "test_specs";
    let mut valid_count = 0;
    let mut invalid_count = 0;
    let mut impl_defined_count = 0;

    // Process all test files
    for entry in fs::read_dir(test_specs_dir)? {
        let entry = entry?;
        let path = entry.path();

        if path.extension().and_then(|s| s.to_str()) == Some("json") {
            let file_name = path.file_name().unwrap().to_str().unwrap();
            let content = fs::read(&path)?;

            // Determine category based on prefix
            let is_valid = file_name.starts_with("y_");
            let is_invalid = file_name.starts_with("n_");
            let is_implementation_defined = file_name.starts_with("i_");

            if is_valid {
                process_valid_file(file_name, &content)?;
                valid_count += 1;
            } else if is_invalid {
                process_invalid_file(file_name, &content)?;
                invalid_count += 1;
            } else if is_implementation_defined {
                process_impl_defined_file(file_name, &content)?;
                impl_defined_count += 1;
            }
        }
    }

    // Add seed inputs for better fuzzing coverage
    add_seed_inputs()?;

    println!("Corpus generation complete!");
    println!("  Valid JSON files: {}", valid_count);
    println!("  Invalid JSON files: {}", invalid_count);
    println!("  Implementation-defined files: {}", impl_defined_count);
    println!();
    println!("Next steps:");
    println!("1. Install cargo-fuzz: cargo install cargo-fuzz");
    println!("2. Initialize fuzzing: cargo fuzz init");
    println!("3. Run fuzzers:");
    println!("   cargo fuzz run parse_json");
    println!("   cargo fuzz run tokenize_json");

    Ok(())
}

fn process_valid_file(file_name: &str, content: &[u8]) -> Result<(), Box<dyn std::error::Error>> {
    // Store in organized corpus
    let dest_path = format!("corpus/valid/{}", file_name);
    fs::write(&dest_path, content)?;

    // Add to all fuzz corpora (valid files should parse successfully)
    add_to_fuzz_corpus("parse_json", file_name, content)?;
    add_to_fuzz_corpus("tokenize_json", file_name, content)?;

    // Add specific types to targeted fuzzers
    if file_name.contains("number") {
        add_to_fuzz_corpus("parse_numbers", file_name, content)?;
    }
    if file_name.contains("string") {
        add_to_fuzz_corpus("parse_strings", file_name, content)?;
    }

    println!("  ✓ Valid: {}", file_name);
    Ok(())
}

fn process_invalid_file(file_name: &str, content: &[u8]) -> Result<(), Box<dyn std::error::Error>> {
    let dest_path = format!("corpus/invalid/{}", file_name);
    fs::write(&dest_path, content)?;

    // Add to fuzz corpora (should fail gracefully without panics)
    add_to_fuzz_corpus("parse_json", file_name, content)?;
    add_to_fuzz_corpus("tokenize_json", file_name, content)?;

    if file_name.contains("number") {
        add_to_fuzz_corpus("parse_numbers", file_name, content)?;
    }
    if file_name.contains("string") {
        add_to_fuzz_corpus("parse_strings", file_name, content)?;
    }

    println!("  ✗ Invalid: {}", file_name);
    Ok(())
}

fn process_impl_defined_file(
    file_name: &str,
    content: &[u8],
) -> Result<(), Box<dyn std::error::Error>> {
    let dest_path = format!("corpus/implementation_defined/{}", file_name);
    fs::write(&dest_path, content)?;

    add_to_fuzz_corpus("parse_json", file_name, content)?;

    println!("  ? Impl-defined: {}", file_name);
    Ok(())
}

fn add_to_fuzz_corpus(
    target: &str,
    file_name: &str,
    content: &[u8],
) -> Result<(), Box<dyn std::error::Error>> {
    let fuzz_dest = format!("fuzz/corpus/{}/{}", target, file_name);
    fs::write(&fuzz_dest, content)?;
    Ok(())
}

fn add_seed_inputs() -> Result<(), Box<dyn std::error::Error>> {
    println!("Adding seed inputs...");

    // Simple approach: define seeds as string literals and convert to bytes
    let seed_data = [
        ("null", "seed_null.json"),
        ("true", "seed_true.json"),
        ("false", "seed_false.json"),
        ("0", "seed_zero.json"),
        ("-1", "seed_negative.json"),
        ("123", "seed_int.json"),
        ("3.14", "seed_float.json"),
        ("-3.14e-10", "seed_scientific.json"),
        ("\"\"", "seed_empty_string.json"),
        ("\"hello\"", "seed_string.json"),
        ("[]", "seed_empty_array.json"),
        ("[1,2,3]", "seed_simple_array.json"),
        ("[null,true,false]", "seed_mixed_array.json"),
        ("{}", "seed_empty_object.json"),
        ("{\"key\":\"value\"}", "seed_simple_object.json"),
        ("{\"a\":1,\"b\":[2,3]}", "seed_nested_object.json"),
    ];

    for (json_str, filename) in seed_data.iter() {
        let content = json_str.as_bytes();

        add_to_fuzz_corpus("parse_json", filename, content)?;
        add_to_fuzz_corpus("tokenize_json", filename, content)?;

        if filename.contains("number")
            || filename.contains("int")
            || filename.contains("float")
            || filename.contains("scientific")
        {
            add_to_fuzz_corpus("parse_numbers", filename, content)?;
        }
        if filename.contains("string") {
            add_to_fuzz_corpus("parse_strings", filename, content)?;
        }
    }

    println!("  Added {} seed inputs", seed_data.len());
    Ok(())
}
