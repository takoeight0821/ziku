#!/bin/bash
set -e

if [ -z "$1" ]; then
  echo "Usage: $0 <issue-number-or-url>"
  exit 1
fi

ISSUE="$1"

# Use gh to view the issue. json output is easier to parse reliably if we needed structured data,
# but for human/LLM readability, standard output is often fine.
# However, LLMs parse structured text better. Let's use standard view but ensure we get body.

gh issue view "$ISSUE"
