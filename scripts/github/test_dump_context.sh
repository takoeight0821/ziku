#!/bin/bash
set -e

# Mock gh
gh() {
  if [[ "$1" == "issue" && "$2" == "view" ]]; then
    if [[ "$*" == *"--comments"* ]]; then
        echo "title:	Test Issue"
        echo "body:	Test Body"
        echo "--"
        echo "author:	User1"
        echo "body:	Comment 1"
    else
        echo "title:	Test Issue"
        echo "body:	Test Body"
    fi
    return 0
  fi
  if [[ "$1" == "pr" && "$2" == "list" ]]; then
    echo "124	Test PR	OPEN"
    return 0
  fi
  command gh "$@"
}
export -f gh

# Mock git
git() {
  if [[ "$1" == "rev-parse" ]]; then
    echo "task/123-test-task"
    return 0
  fi
  command git "$@"
}
export -f git

echo "Testing dump_context.sh..."

OUTPUT=$(./scripts/github/dump_context.sh)

echo "$OUTPUT"

if [[ "$OUTPUT" == *"# Context: Issue #123"* ]]; then
  echo "✅ Context found."
else
  echo "❌ Context missing."
  exit 1
fi

if [[ "$OUTPUT" == *"Test Body"* ]]; then
  echo "✅ Body found."
else
  echo "❌ Body missing."
  exit 1
fi
