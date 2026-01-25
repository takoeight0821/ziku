#!/bin/bash
# Hook: Warn when modifying files in Proofs/ directory
# Called by PreToolUse (Edit|Write)

# Read JSON from stdin
input=$(cat)

# Extract file_path
file_path=$(echo "$input" | jq -r '.tool_input.file_path // empty')

# Exit if file_path is empty
if [ -z "$file_path" ]; then
    exit 0
fi

# Detect modifications to Proofs/ directory
if [[ "$file_path" == *"Proofs/"* ]] || [[ "$file_path" == *"/Proofs/"* ]]; then
    echo "WARNING: Modifying file in Proofs/ directory: $file_path" >&2
    echo "Please ensure:" >&2
    echo "  - No 'sorry' is introduced" >&2
    echo "  - All proofs remain complete" >&2
    echo "  - Use /proof-writing skill for guidelines" >&2
fi

# Warning only, do not block
exit 0
