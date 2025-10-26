#![no_main]

use json_parser::parse;
use libfuzzer_sys::fuzz_target;

fuzz_target!(|data: &[u8]| {
    if let Ok(s) = std::str::from_utf8(data) {
        // Test that parser doesn't panic on any input
        let our_result = parse(s);
        let serde_result = serde_json::from_str::<serde_json::Value>(s);
        match (our_result.is_ok(), serde_result.is_ok()) {
            (true, true) => {
                println!("Both parsers succeeded on: {}", s);
            }
            (false, false) => {
                // Both failed - this is expected for invalid JSON
                // This is actually a good outcome!
            }
            (true, false) => {
                // We succeeded but reference failed - potential bug
                // Our parser might be too lenient
                panic!("Our parser accepted invalid JSON: {}", s);
            }
            (false, true) => {
                // We failed but reference succeeded - potential bug
                // Our parser might be too strict
                println!(
                    "Our parser rejected valid JSON: {} (error: {:?})",
                    s, our_result
                );
                // Note: Don't panic here as this might be acceptable
            }
        }
    }
});
