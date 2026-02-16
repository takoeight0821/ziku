#!/bin/bash
# Hook: Run tests after creating test files
# Called by PostToolUse (Write)

# Read JSON from stdin
input=$(cat)

# Extract file_path
file_path=$(echo "$input" | jq -r '.tool_input.file_path // empty')

# Exit if file_path is empty
if [ -z "$file_path" ]; then
    exit 0
fi

# Only run tests for .ziku files in tests/ directory
if [[ "$file_path" == *"tests/"* ]] && [[ "$file_path" == *.ziku ]]; then
    echo "Running tests after creating: $file_path" >&2

    # Move to project root and run tests
    cd "$CLAUDE_PROJECT_DIR" || exit 0

    # Run lake test
    if ! lake test 2>&1; then
        echo "Tests failed after creating $file_path" >&2
        # Exit code 2 to block
        exit 2
    fi

    echo "Tests passed" >&2
fi

exit 0
