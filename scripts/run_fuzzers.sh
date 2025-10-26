
#!/bin/bash

echo "Starting JSON Parser Fuzzing Suite"
echo "=================================="

# Generate corpus from test specs
echo "Generating corpus..."
cargo run --bin generate_corpus

echo ""
echo "Available fuzz targets:"
echo "1. parse_json - General JSON parsing"
echo "2. tokenize_json - JSON tokenization"
echo "3. parse_numbers - Number parsing edge cases"
echo "4. parse_strings - String parsing edge cases"

if [ $# -eq 0 ]; then
    echo ""
    echo "Usage: $0 [target_name] [duration_seconds]"
    echo "Example: $0 parse_json 60"
    echo ""
    echo "Running parse_json for 30 seconds by default..."
    TARGET="parse_json"
    DURATION="30"
else
    TARGET=$1
    DURATION=${2:-30}
fi

echo ""
echo "Running fuzzer: $TARGET for ${DURATION}s"
echo "Press Ctrl+C to stop early"

# Run the fuzzer
timeout ${DURATION}s cargo fuzz run $TARGET -- -max_total_time=${DURATION}

echo ""
echo "Fuzzing complete. Check fuzz/artifacts/ for any crashes found."
