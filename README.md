## JSON Parser
This is the hobby project of mine for learning more about zero-copy parsing, SIMD in Rust. This is just the start.
Currently, the parser is able to parse JSON objects and arrays, and checks the boxes for most valid and invalid json files.

## Caveats
Not all JSON parsers agree on the same specification. The filenames, starting with `i_` are dependent on parsers and each parsers handle them differently.
- Big Integer
- Utf16 support

## Goals
- Use SIMD
- Support for diagnostics
- Zerocopy Parsing (Avoid allocations, and just try to move the buffer)
- Implement fuzzing to discover new issues
- Try to write everything from scratch and avoid dependencies
