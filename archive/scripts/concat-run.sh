#!/bin/bash
# Concatenate multiple Ziku files and run/compile them
# Usage: ./scripts/concat-run.sh [--scheme] file1.ziku file2.ziku ...
# With --scheme: outputs compiled Scheme code
# Without: runs the compiled Scheme code

set -e

SCRIPT_DIR="$(cd "$(dirname "$0")" && pwd)"
PROJECT_DIR="$(dirname "$SCRIPT_DIR")"
TMP_SCM="$PROJECT_DIR/.mal_tmp.scm"

SCHEME_MODE=false
if [ "$1" = "--scheme" ]; then
    SCHEME_MODE=true
    shift
fi

if [ $# -eq 0 ]; then
    echo "Usage: $0 [--scheme] file1.ziku [file2.ziku ...]" >&2
    exit 1
fi

# Concatenate all ziku files
COMBINED=$(cat "$@")

if [ "$SCHEME_MODE" = true ]; then
    # Compile to Scheme
    echo "$COMBINED" | docker compose run --rm -T ziku lake exe ziku --scheme 2>/dev/null
else
    # Run with Scheme interpreter
    echo "$COMBINED" | docker compose run --rm -T ziku lake exe ziku --scheme 2>/dev/null > "$TMP_SCM"
    docker compose run --rm -T ziku scheme .mal_tmp.scm
fi
