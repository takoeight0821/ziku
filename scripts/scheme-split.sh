#!/bin/bash
# Split generated Scheme code into runtime and main parts
# Usage: ./scripts/scheme-split.sh INPUT OUTPUT_PREFIX
#
# This script splits a Ziku-generated Scheme file into two parts:
#   OUTPUT_PREFIX-runtime.scm  - Runtime library (ziku-* definitions)
#   OUTPUT_PREFIX-main.scm     - Main program (user code)
#
# The split point is determined by:
#   1. Looking for "; --- Generated from source ---" marker
#   2. Fallback: first define that doesn't start with "ziku-"

set -e

show_help() {
    head -n 12 "$0" | tail -n +2 | sed 's/^# //' | sed 's/^#//'
    echo ""
    echo "Examples:"
    echo "  $0 .mal_tmp.scm /tmp/output"
    echo "  # Creates: /tmp/output-runtime.scm and /tmp/output-main.scm"
}

if [ "$1" = "-h" ] || [ "$1" = "--help" ]; then
    show_help
    exit 0
fi

if [ $# -lt 2 ]; then
    show_help
    exit 1
fi

INPUT="$1"
OUTPUT_PREFIX="$2"

if [ ! -f "$INPUT" ]; then
    echo "Error: Input file '$INPUT' not found" >&2
    exit 1
fi

# Find the marker that separates runtime from main
marker_line=$(grep -n '; --- Generated from source ---' "$INPUT" 2>/dev/null | head -1 | cut -d: -f1 || echo "")

if [ -z "$marker_line" ]; then
    # Fallback: look for the first non-runtime define
    marker_line=$(grep -n '^(define ' "$INPUT" 2>/dev/null | grep -v 'ziku-' | head -1 | cut -d: -f1 || echo "")
fi

if [ -z "$marker_line" ]; then
    echo "Warning: Could not find section marker" >&2
    echo "Creating single output file at ${OUTPUT_PREFIX}-main.scm" >&2
    cp "$INPUT" "${OUTPUT_PREFIX}-main.scm"
    touch "${OUTPUT_PREFIX}-runtime.scm"
    exit 0
fi

total=$(wc -l < "$INPUT" | tr -d ' ')

# Split the file
head -n "$((marker_line - 1))" "$INPUT" > "${OUTPUT_PREFIX}-runtime.scm"
tail -n "+$marker_line" "$INPUT" > "${OUTPUT_PREFIX}-main.scm"

runtime_lines=$(wc -l < "${OUTPUT_PREFIX}-runtime.scm" | tr -d ' ')
main_lines=$(wc -l < "${OUTPUT_PREFIX}-main.scm" | tr -d ' ')

echo "Split complete:"
echo "  Runtime: ${OUTPUT_PREFIX}-runtime.scm ($runtime_lines lines)"
echo "  Main:    ${OUTPUT_PREFIX}-main.scm ($main_lines lines)"
