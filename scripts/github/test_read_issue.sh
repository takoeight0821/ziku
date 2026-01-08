#!/bin/bash
set -e

# Mock gh
gh() {
  if [[ "$1" == "issue" && "$2" == "view" ]]; then
    echo "title:	Test Issue Title"
    echo "body:	This is the test body content."
    return 0
  fi
  command gh "$@"
}
export -f gh

echo "Testing read_issue.sh..."
OUTPUT=$(./scripts/github/read_issue.sh 123)

if [[ "$OUTPUT" == *"Test Issue Title"* ]] && [[ "$OUTPUT" == *"This is the test body content."* ]]; then
  echo "✅ Output contains title and body."
else
  echo "❌ Output missing content."
  echo "$OUTPUT"
  exit 1
fi
