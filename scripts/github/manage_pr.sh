#!/bin/bash
set -e

if [ "$#" -lt 3 ]; then
  echo "Usage: $0 <action> <arg1> <arg2>"
  echo "Actions:"
  echo "  create <title> <body>"
  echo "  update <pr-number-or-url> <title> <body>"
  exit 1
fi

ACTION="$1"

if [ "$ACTION" == "create" ]; then
  TITLE="$2"
  BODY="$3"
  
  # Ensure the branch is pushed to origin to avoid interactive prompts
  CURRENT_BRANCH=$(git rev-parse --abbrev-ref HEAD)
  echo "Pushing $CURRENT_BRANCH to origin..."
  git push -u origin "$CURRENT_BRANCH"

  gh pr create --title "$TITLE" --body "$BODY"
elif [ "$ACTION" == "update" ]; then
  if [ "$#" -lt 4 ]; then
     echo "Usage: $0 update <pr> <title> <body>"
     exit 1
  fi
  PR="$2"
  TITLE="$3"
  BODY="$4"
  gh pr edit "$PR" --title "$TITLE" --body "$BODY"
else
  echo "❌ Unknown action: $ACTION"
  exit 1
fi
