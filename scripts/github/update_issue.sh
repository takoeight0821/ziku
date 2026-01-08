#!/bin/bash
set -e

if [ "$#" -lt 3 ]; then
  echo "Usage: $0 <issue-number-or-url> <action> <content>"
  echo "Actions: comment, body"
  exit 1
fi

ISSUE="$1"
ACTION="$2"
CONTENT="$3"

if [ "$ACTION" == "comment" ]; then
  gh issue comment "$ISSUE" --body "$CONTENT"
elif [ "$ACTION" == "body" ]; then
  gh issue edit "$ISSUE" --body "$CONTENT"
else
  echo "❌ Unknown action: $ACTION"
  exit 1
fi
