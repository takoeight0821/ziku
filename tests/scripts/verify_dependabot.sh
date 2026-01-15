#!/bin/bash
# Verify dependabot.yml has cooldown configured for all ecosystems
FILE=".github/dependabot.yml"

if [[ ! -f "$FILE" ]]; then
  echo "Error: $FILE not found"
  exit 1
fi

# Check for cooldown block and default-days: 7
# We expect 3 occurrences because there are 3 ecosystems
COUNT=$(grep -c "default-days: 7" "$FILE")

if [[ "$COUNT" -eq 3 ]]; then
  echo "PASS: Cooldown found for 3 ecosystems"
  exit 0
else
  echo "FAIL: Expected 3 ecosystems with cooldown, found $COUNT"
  exit 1
fi
