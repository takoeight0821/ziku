#!/bin/bash
# Ziku test helper script
# Usage: ./scripts/ziku-test.sh <phase> <expression-or-file>
# Phases: parse, infer, eval, translate, scheme

set -e

PHASE="${1:-eval}"
INPUT="${2:-}"

if [[ -z "$INPUT" ]]; then
    echo "Usage: $0 <phase> <expression-or-file>"
    echo "Phases: parse, infer, eval, translate, scheme, scheme-run"
    echo ""
    echo "Examples:"
    echo "  $0 infer 'let x = 1 in x + 1'"
    echo "  $0 eval tests/golden/parser/success/arithmetic.ziku"
    echo "  $0 scheme-run '(\\x -> x + 1)(41)'"
    exit 1
fi

# Check if input is a file
if [[ -f "$INPUT" ]]; then
    EXPR=$(cat "$INPUT")
else
    EXPR="$INPUT"
fi

# Build if needed
if [[ ! -f .lake/build/bin/ziku-test ]]; then
    echo "Building Ziku..." >&2
    lake build >&2
fi

case "$PHASE" in
    parse)
        echo "$EXPR" | lake exe ziku-test parse
        ;;
    infer)
        echo "$EXPR" | lake exe ziku-test infer
        ;;
    eval)
        echo "$EXPR" | lake exe ziku-test eval
        ;;
    translate)
        echo "$EXPR" | lake exe ziku-test translate
        ;;
    scheme)
        echo "$EXPR" | lake exe ziku-test scheme
        ;;
    scheme-run)
        SCHEME_CODE=$(echo "$EXPR" | lake exe ziku-test scheme)
        echo "$SCHEME_CODE" | scheme --script /dev/stdin
        ;;
    *)
        echo "Unknown phase: $PHASE" >&2
        echo "Valid phases: parse, infer, eval, translate, scheme, scheme-run" >&2
        exit 1
        ;;
esac
