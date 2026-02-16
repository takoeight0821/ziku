#!/bin/bash
set -e
echo "Running MAL Step 0 Test..."
OUTPUT=$(echo "hello world" | ./examples/mal/run examples/mal/step0_repl.ziku 2>/dev/null)
echo "Output was: '$OUTPUT'"
if [[ "$OUTPUT" == *"hello world"* ]]; then
  echo "Test PASSED: Output matched expected."
else
  echo "Test FAILED: Output did not match."
  exit 1
fi
