#!/bin/bash
set -e

SKIP_CONFIRM=false
DESCRIPTION=""

while [[ $# -gt 0 ]]; do
  case $1 in
    -y|--yes)
      SKIP_CONFIRM=true
      shift
      ;;
    *)
      if [ -z "$DESCRIPTION" ]; then
        DESCRIPTION="$1"
      else
        echo "Unknown argument: $1"
        exit 1
      fi
      shift
      ;;
  esac
done

if [ -z "$DESCRIPTION" ]; then
    echo "Usage: $0 [-y|--yes] <task-description> [body-file]"
    exit 1
fi

BODY_FILE="$2"

# Slugify: lowercase, replace non-alphanumeric with hyphens, remove multiple hyphens, trim hyphens
SLUG=$(echo "$DESCRIPTION" | tr '[:upper:]' '[:lower:]' | sed 's/[^a-z0-9]/-/g' | sed 's/--*/-/g' | sed 's/^-//;s/-$//')

# Determine body content
if [ -n "$BODY_FILE" ] && [ -f "$BODY_FILE" ]; then
    BODY=$(cat "$BODY_FILE")
else
    # Read template and strip frontmatter (the part between --- and ---)
    TEMPLATE_PATH=".github/ISSUE_TEMPLATE/task.md"
    if [ -f "$TEMPLATE_PATH" ]; then
        BODY=$(sed '1,/^---$/d' "$TEMPLATE_PATH")
    else
        BODY="Task description for: $DESCRIPTION"
    fi
fi

if [ "$SKIP_CONFIRM" = false ]; then
    echo "----------------------------------------"
    echo "PROPOSED GITHUB ISSUE:"
    echo "Title: $DESCRIPTION"
    echo "Body:"
    echo "$BODY"
    echo "----------------------------------------"
    read -p "Do you want to create this issue? (y/N): " confirm
    if [[ ! "$confirm" =~ ^[Yy]$ ]]; then
        echo "Aborting."
        exit 0
    fi
fi

echo "Creating GitHub issue for: $DESCRIPTION"
ISSUE_URL=$(gh issue create --title "$DESCRIPTION" --body "$BODY")

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
