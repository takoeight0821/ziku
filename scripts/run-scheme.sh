#!/bin/bash
# run-scheme.sh - Compile Ziku to Scheme and run with Chez Scheme
#
# Usage:
#   ./scripts/run-scheme.sh file.ziku         # Run from file
#   echo "1 + 2" | ./scripts/run-scheme.sh    # Run from stdin
#   ./scripts/run-scheme.sh -c "1 + 2"        # Run inline code
#   ./scripts/run-scheme.sh -d file.ziku      # Debug mode (show generated code)

set -e

SCRIPT_DIR="$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)"
PROJECT_DIR="$(dirname "$SCRIPT_DIR")"
SCHEME_BACKEND="$PROJECT_DIR/.lake/build/bin/scheme-backend"

# Check if scheme-backend exists
if [ ! -f "$SCHEME_BACKEND" ]; then
    echo "Error: scheme-backend not found. Run 'lake build' first." >&2
    exit 1
fi

# Parse arguments
DEBUG=false
CODE=""
INPUT_FILE=""

while [[ $# -gt 0 ]]; do
    case $1 in
        -d|--debug)
            DEBUG=true
            shift
            ;;
        -c|--code)
            CODE="$2"
            shift 2
            ;;
        -h|--help)
            echo "Usage: $0 [OPTIONS] [FILE]"
            echo ""
            echo "Compile Ziku code to Scheme and run with Chez Scheme."
            echo ""
            echo "Options:"
            echo "  -c, --code CODE   Run inline code"
            echo "  -d, --debug       Show generated Scheme code before running"
            echo "  -h, --help        Show this help message"
            echo ""
            echo "Examples:"
            echo "  $0 file.ziku              Run from file"
            echo "  echo '1 + 2' | $0         Run from stdin"
            echo "  $0 -c '1 + 2'             Run inline code"
            echo "  $0 -d file.ziku           Debug mode"
            exit 0
            ;;
        *)
            INPUT_FILE="$1"
            shift
            ;;
    esac
done

# Create temp file for Scheme output
TEMP_SS=$(mktemp /tmp/ziku_XXXXXX.ss)
trap "rm -f $TEMP_SS" EXIT

# Compile to Scheme
if [ -n "$CODE" ]; then
    # Inline code
    echo "$CODE" | "$SCHEME_BACKEND" > "$TEMP_SS"
elif [ -n "$INPUT_FILE" ]; then
    # From file
    "$SCHEME_BACKEND" "$INPUT_FILE" > "$TEMP_SS"
else
    # From stdin
    "$SCHEME_BACKEND" > "$TEMP_SS"
fi

# Debug mode: show generated code
if [ "$DEBUG" = true ]; then
    echo "=== Generated Scheme Code ==="
    cat "$TEMP_SS"
    echo ""
    echo "=== Output ==="
fi

# Run with Chez Scheme
scheme --script "$TEMP_SS"
