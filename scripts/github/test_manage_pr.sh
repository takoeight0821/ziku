#!/bin/bash
set -e

# Mock gh
gh() {
  if [[ "$1" == "pr" && "$2" == "create" ]]; then
    echo "https://github.com/takoeight0821/ziku/pull/124"
    return 0
  fi
  if [[ "$1" == "pr" && "$2" == "edit" ]]; then
    echo "https://github.com/takoeight0821/ziku/pull/124"
    return 0
  fi
  command gh "$@"
}
export -f gh

echo "Testing manage_pr.sh..."

# Test Create
echo "Test 1: Create"
./scripts/github/manage_pr.sh create "Feat: New Feature" "Closes #123"

# Test Update
echo "Test 2: Update"
./scripts/github/manage_pr.sh update 124 "Feat: Updated Feature" "Updated body"

echo "✅ Tests passed."
