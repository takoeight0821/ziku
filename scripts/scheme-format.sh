#!/bin/bash
# Format S-expressions with proper indentation using Chez Scheme's pretty-print
# Usage: ./scripts/scheme-format.sh [FILE]
#        cat file.scm | ./scripts/scheme-format.sh
#
# Reads S-expressions from FILE or stdin and outputs formatted code.
# Uses Chez Scheme's built-in pretty-print for consistent formatting.

set -e

show_help() {
    head -n 8 "$0" | tail -n +2 | sed 's/^# //' | sed 's/^#//'
    echo ""
    echo "Examples:"
    echo "  $0 .mal_tmp.scm"
    echo "  ./scripts/scheme-analyze.sh --section main .mal_tmp.scm | $0"
    echo "  ./scripts/scheme-analyze.sh --search \"define ziku-eval\" .mal_tmp.scm | $0"
}

if [ "$1" = "-h" ] || [ "$1" = "--help" ]; then
    show_help
    exit 0
fi

# Create a temporary Scheme script for pretty-printing
format_scheme='
(define (format-all port)
  (let loop ()
    (let ([expr (read port)])
      (unless (eof-object? expr)
        (pretty-print expr)
        (newline)
        (loop)))))

(if (null? (command-line-arguments))
    (format-all (current-input-port))
    (call-with-input-file (car (command-line-arguments))
      format-all))
'

if [ -n "$1" ] && [ -f "$1" ]; then
    # File argument provided
    echo "$format_scheme" | scheme --quiet --script /dev/stdin "$1" 2>/dev/null || {
        echo "Error: Failed to format file. Is Chez Scheme installed?" >&2
        echo "Falling back to cat..." >&2
        cat "$1"
    }
else
    # Read from stdin - save to temp file first since Scheme read needs seekable input
    tmpfile=$(mktemp)
    trap 'rm -f "$tmpfile"' EXIT
    cat > "$tmpfile"

    if [ -s "$tmpfile" ]; then
        echo "$format_scheme" | scheme --quiet --script /dev/stdin "$tmpfile" 2>/dev/null || {
            echo "Error: Failed to format input. Is Chez Scheme installed?" >&2
            echo "Falling back to cat..." >&2
            cat "$tmpfile"
        }
    fi
fi
