#!/bin/bash
# Hook: Run build after editing Lean files
# Called by PostToolUse (Edit)

# Read JSON from stdin
input=$(cat)

# Extract file_path
file_path=$(echo "$input" | jq -r '.tool_input.file_path // empty')

# Exit if file_path is empty
if [ -z "$file_path" ]; then
    exit 0
fi

# Only run build for .lean files
if [[ "$file_path" == *.lean ]]; then
    echo "Building Lean project after editing: $file_path" >&2

    # Move to project root and build
    cd "$CLAUDE_PROJECT_DIR" || exit 0

    # Run lake build
    if ! lake build 2>&1; then
        echo "Build failed for $file_path" >&2
        # Exit code 2 to block
        exit 2
    fi

    echo "Build succeeded" >&2
fi

exit 0
