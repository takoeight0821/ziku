#!/bin/bash
set -e

if [ -z "$1" ]; then
    echo "Usage: $0 <task-description>"
    exit 1
fi

DESCRIPTION="$1"
# Slugify: lowercase, replace non-alphanumeric with hyphens, remove multiple hyphens, trim hyphens
SLUG=$(echo "$DESCRIPTION" | tr '[:upper:]' '[:lower:]' | sed 's/[^a-z0-9]/-/g' | sed 's/--*/-/g' | sed 's/^-//;s/-$//')

echo "Creating GitHub issue for: $DESCRIPTION"

# Create issue using the task template
# Note: We use --template task.md if it exists, otherwise it falls back to default or prompts
# Since we just created it, it should work.
ISSUE_URL=$(gh issue create --title "$DESCRIPTION" --template task.md)

if [ -z "$ISSUE_URL" ]; then
    echo "❌ Failed to create issue."
    exit 1
fi

# Extract issue number from URL (e.g., https://github.com/user/repo/issues/123 -> 123)
ISSUE_NUMBER=$(echo "$ISSUE_URL" | grep -oE '[0-9]+$')

BRANCH_NAME="task/${ISSUE_NUMBER}-${SLUG}"

echo "Creating and linking branch: $BRANCH_NAME"
gh issue develop "$ISSUE_NUMBER" --name "$BRANCH_NAME" --checkout

echo "✅ Task initialized successfully."
echo "Issue: $ISSUE_URL"
echo "Branch: $BRANCH_NAME"
