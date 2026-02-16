#!/bin/bash
# Scheme file analyzer for large generated code
# Usage: ./scripts/scheme-analyze.sh [OPTIONS] FILE
#
# Options:
#   --stats             Show file statistics (lines, chars, defines, lambdas)
#   --functions         List function definitions (with line numbers, max 100)
#   --head N            Show first N lines
#   --tail N            Show last N lines
#   --range START END   Show lines from START to END (1-indexed)
#   --section TYPE      Extract runtime or main section (TYPE: runtime|main)
#   --search PATTERN    Search for pattern with context
#   -h, --help          Show this help message

set -e

show_help() {
    head -n 14 "$0" | tail -n +2 | sed 's/^# //' | sed 's/^#//'
    echo ""
    echo "Examples:"
    echo "  $0 --stats .mal_tmp.scm"
    echo "  $0 --functions .mal_tmp.scm"
    echo "  $0 --section main .mal_tmp.scm"
    echo "  $0 --search \"ziku-eval\" .mal_tmp.scm"
}

stats() {
    local file="$1"
    echo "=== File Statistics ==="
    echo "File: $file"
    echo "Size: $(wc -c < "$file" | tr -d ' ') bytes"
    echo "Lines: $(wc -l < "$file" | tr -d ' ')"
    echo "Defines: $(grep -c '(define ' "$file" 2>/dev/null || echo 0)"
    echo "Lambdas: $(grep -c '(lambda ' "$file" 2>/dev/null || echo 0)"
    echo "Let expressions: $(grep -c '(let ' "$file" 2>/dev/null || echo 0)"

    # Top-level define count (rough estimate)
    echo ""
    echo "=== Top-level definitions (first 20) ==="
    grep -n '^(define ' "$file" 2>/dev/null | head -20 || echo "(none found)"
}

functions() {
    local file="$1"
    echo "=== Function Definitions (max 100) ==="
    # Match (define name or (define (name
    grep -n '(define ' "$file" 2>/dev/null | head -100 | while read -r line; do
        # Extract line number and definition
        lineno=$(echo "$line" | cut -d: -f1)
        content=$(echo "$line" | cut -d: -f2-)
        # Try to extract function name
        name=$(echo "$content" | sed -E 's/.*\(define \(?([^ ()]+).*/\1/')
        printf "%6d: %s\n" "$lineno" "$name"
    done
}

head_lines() {
    local file="$1"
    local n="$2"
    head -n "$n" "$file" | nl -ba
}

tail_lines() {
    local file="$1"
    local n="$2"
    local total
    total=$(wc -l < "$file" | tr -d ' ')
    local start=$((total - n + 1))
    if [ "$start" -lt 1 ]; then
        start=1
    fi
    tail -n "$n" "$file" | nl -ba -v "$start"
}

range_lines() {
    local file="$1"
    local start="$2"
    local end="$3"
    sed -n "${start},${end}p" "$file" | nl -ba -v "$start"
}

section() {
    local file="$1"
    local type="$2"

    # Find the marker comment that separates runtime from main
    # Ziku generates: ; --- Generated from source ---
    local marker_line
    marker_line=$(grep -n '; --- Generated from source ---' "$file" 2>/dev/null | head -1 | cut -d: -f1 || echo "")

    if [ -z "$marker_line" ]; then
        # Fallback: look for the first non-runtime define
        # Runtime definitions typically start with ziku- prefix
        # Find first define that doesn't match runtime pattern
        marker_line=$(grep -n '^(define ' "$file" 2>/dev/null | grep -v 'ziku-' | head -1 | cut -d: -f1 || echo "")
    fi

    if [ -z "$marker_line" ]; then
        echo "Warning: Could not find section marker, outputting entire file" >&2
        cat "$file"
        return
    fi

    local total
    total=$(wc -l < "$file" | tr -d ' ')

    case "$type" in
        runtime)
            head -n "$((marker_line - 1))" "$file"
            ;;
        main)
            tail -n "+$marker_line" "$file"
            ;;
        *)
            echo "Error: Unknown section type '$type'. Use 'runtime' or 'main'." >&2
            exit 1
            ;;
    esac
}

search_pattern() {
    local file="$1"
    local pattern="$2"
    echo "=== Searching for: $pattern ==="
    grep -n -B2 -A5 "$pattern" "$file" 2>/dev/null | head -200 || echo "(no matches found)"
}

# Main
if [ $# -eq 0 ]; then
    show_help
    exit 1
fi

case "$1" in
    -h|--help)
        show_help
        exit 0
        ;;
    --stats)
        if [ -z "$2" ]; then
            echo "Error: --stats requires a file argument" >&2
            exit 1
        fi
        stats "$2"
        ;;
    --functions)
        if [ -z "$2" ]; then
            echo "Error: --functions requires a file argument" >&2
            exit 1
        fi
        functions "$2"
        ;;
    --head)
        if [ -z "$2" ] || [ -z "$3" ]; then
            echo "Error: --head requires N and FILE arguments" >&2
            exit 1
        fi
        head_lines "$3" "$2"
        ;;
    --tail)
        if [ -z "$2" ] || [ -z "$3" ]; then
            echo "Error: --tail requires N and FILE arguments" >&2
            exit 1
        fi
        tail_lines "$3" "$2"
        ;;
    --range)
        if [ -z "$2" ] || [ -z "$3" ] || [ -z "$4" ]; then
            echo "Error: --range requires START END FILE arguments" >&2
            exit 1
        fi
        range_lines "$4" "$2" "$3"
        ;;
    --section)
        if [ -z "$2" ] || [ -z "$3" ]; then
            echo "Error: --section requires TYPE and FILE arguments" >&2
            exit 1
        fi
        section "$3" "$2"
        ;;
    --search)
        if [ -z "$2" ] || [ -z "$3" ]; then
            echo "Error: --search requires PATTERN and FILE arguments" >&2
            exit 1
        fi
        search_pattern "$3" "$2"
        ;;
    *)
        echo "Error: Unknown option '$1'" >&2
        show_help
        exit 1
        ;;
esac
