#!/bin/bash
set -e

# Mocking gh to avoid actual network calls during tests
gh() {
  if [[ "$1" == "issue" && "$2" == "create" ]]; then
    echo "https://github.com/takoeight0821/ziku/issues/123"
    return 0
  fi
  if [[ "$1" == "issue" && "$2" == "develop" ]]; then
    # find --name flag
    local name=""
    shift 2
    while [[ $# -gt 0 ]]; do
      if [[ "$1" == "--name" ]]; then
        name="$2"
        break
      fi
      shift
    done
    git checkout -b "$name"
    return 0
  fi
  command gh "$@"
}
export -f gh

# Setup
TEST_DESC="Test task initialization"
SLUG="test-task-initialization"

echo "Running task init test..."

# Run the command (to be implemented)
# We expect it to create a branch task/123-test-task-initialization
./scripts/task-init.sh "$TEST_DESC"

# Verify branch creation
CURRENT_BRANCH=$(git rev-parse --abbrev-ref HEAD)
EXPECTED_BRANCH="task/123-$SLUG"

if [[ "$CURRENT_BRANCH" == "$EXPECTED_BRANCH" ]]; then
    echo "✅ Branch created correctly: $CURRENT_BRANCH"
else
    echo "❌ Expected branch $EXPECTED_BRANCH, but got $CURRENT_BRANCH"
    exit 1
fi

# Cleanup
git checkout -
git branch -D "$EXPECTED_BRANCH"

echo "✅ Test passed."
