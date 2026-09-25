#!/bin/bash
# Hook: Warn about randomly-named plan files that violate naming convention
# Triggered by: Stop hook (when Claude finishes responding)
# Convention: YYYY-MM-DD-descriptive-title.md

# Read JSON input (Stop hook provides session context)
input=$(cat)

# Use CLAUDE_PROJECT_DIR if available, fallback to current dir
PLANS_DIR="${CLAUDE_PROJECT_DIR:-.}/.claude/plans"

# Exit silently if plans directory doesn't exist
[ -d "$PLANS_DIR" ] || exit 0

# Check for files with random names (not starting with YYYY-MM-DD)
violations=()
while IFS= read -r file; do
    basename=$(basename "$file" .md)

    # Skip if already date-named (starts with YYYY-MM-DD)
    if [[ "$basename" =~ ^[0-9]{4}-[0-9]{2}-[0-9]{2}- ]]; then
        continue
    fi

    # Skip if doesn't match random pattern (less than 3 word-segments)
    word_count=$(echo "$basename" | tr '-' '\n' | wc -l)
    if [ "$word_count" -lt 3 ]; then
        continue
    fi

    violations+=("$basename")
done < <(find "$PLANS_DIR" -name "*.md" -type f 2>/dev/null)

# Warn if violations found
if [ ${#violations[@]} -gt 0 ]; then
    echo "" >&2
    echo "⚠️  Plan file naming convention violation:" >&2
    echo "" >&2
    for name in "${violations[@]}"; do
        echo "  - $name.md" >&2
    done
    echo "" >&2
    echo "Convention: YYYY-MM-DD-descriptive-title.md" >&2
    echo "Please rename these files to follow the project convention." >&2
    echo "" >&2

    # Exit 2 blocks the stop and feeds stderr to Claude so it can rename the
    # files; exit 0 would leave the warning in the transcript only. Block only
    # when stop_hook_active is explicitly false, so a violation that survives
    # one continuation does not block every later stop.
    if [[ "$input" =~ \"stop_hook_active\"[[:space:]]*:[[:space:]]*false ]]; then
        exit 2
    fi
fi

exit 0
