#!/bin/bash
set -e

# Detect issue from branch name
BRANCH=$(git rev-parse --abbrev-ref HEAD)
if [[ ! "$BRANCH" =~ ^task/([0-9]+)- ]]; then
  echo "❌ Current branch '$BRANCH' does not follow task/<id>-slug pattern."
  exit 1
fi

ISSUE_ID="${BASH_REMATCH[1]}"

echo "# Context: Issue #$ISSUE_ID"
echo ""
echo "## Issue Details"
gh issue view "$ISSUE_ID" --comments
echo ""
echo "## Linked Pull Requests"
# Check if there's a PR for this branch
gh pr list --head "$BRANCH"
