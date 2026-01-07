#!/bin/bash
set -e
echo "Running MAL Step 1 Test..."
# Input: (+ 1 2)
# Output should be: (+ 1 2)
# Because eval is identity, it just reads and prints.
# Note: tokenization might change formatting (spaces).
# Input: (+ 1   2) -> Output: (+ 1 2)

INPUT="(+ 1   2)"
EXPECTED="(+ 1 2)"

OUTPUT=$(echo "$INPUT" | ./examples/mal/run examples/mal/step1_read_print.ziku 2>/dev/null)
# Extract last line (excluding result print)
# Output format:
# (+ 1 2)
# ()

# We check if output contains expected string
if [[ "$OUTPUT" == *"$EXPECTED"* ]]; then
  echo "Test PASSED: Output matched expected."
else
  echo "Test FAILED: Output did not match."
  echo "Expected: '$EXPECTED'"
  echo "Got: '$OUTPUT'"
  exit 1
fi
