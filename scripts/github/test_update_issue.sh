#!/bin/bash
set -e

# Mock gh
gh() {
  if [[ "$1" == "issue" && "$2" == "comment" ]]; then
    echo "https://github.com/takoeight0821/ziku/issues/123#issuecomment-456"
    return 0
  fi
  if [[ "$1" == "issue" && "$2" == "edit" ]]; then
    echo "https://github.com/takoeight0821/ziku/issues/123"
    return 0
  fi
  command gh "$@"
}
export -f gh

echo "Testing update_issue.sh..."

# Test Comment
echo "Test 1: Comment"
./scripts/github/update_issue.sh 123 comment "Test comment"

# Test Body
echo "Test 2: Body"
./scripts/github/update_issue.sh 123 body "New body content"

echo "✅ Tests passed."
