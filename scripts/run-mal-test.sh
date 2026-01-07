#!/bin/bash
set -e

SCRIPT_DIR="$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)"
PROJECT_DIR="$(dirname "$SCRIPT_DIR")"
MAL_DIR="$PROJECT_DIR/vendor/mal"

# Usage: ./scripts/run-mal-test.sh <step>
# Example: ./scripts/run-mal-test.sh step0

if [ -z "$1" ]; then
  echo "Usage: $0 <step>"
  echo "Example: $0 step0"
  exit 1
fi

STEP_NAME="$1"

# Map step name to ziku file and test file
case "$STEP_NAME" in
  step0)
    ZIKU_FILE="examples/mal/step0_repl.ziku"
    TEST_FILE="$MAL_DIR/tests/step0_repl.mal"
    ;;
  step1)
    ZIKU_FILE="examples/mal/step1_read_print.ziku"
    TEST_FILE="$MAL_DIR/tests/step1_read_print.mal"
    ;;
  step2)
    ZIKU_FILE="examples/mal/step2_eval.ziku"
    TEST_FILE="$MAL_DIR/tests/step2_eval.mal"
    ;;
  step3)
    ZIKU_FILE="examples/mal/step3_env.ziku"
    TEST_FILE="$MAL_DIR/tests/step3_env.mal"
    ;;
  step4)
    ZIKU_FILE="examples/mal/step4_if_fn_do.ziku"
    TEST_FILE="$MAL_DIR/tests/step4_if_fn_do.mal"
    ;;
  step5)
    ZIKU_FILE="examples/mal/step5_tco.ziku"
    TEST_FILE="$MAL_DIR/tests/step5_tco.mal"
    ;;
  *)
    echo "Unknown step: $STEP_NAME"
    exit 1
    ;;
esac

# Check if Ziku file exists
if [ ! -f "$PROJECT_DIR/$ZIKU_FILE" ]; then
    echo "Error: Ziku file not found: $ZIKU_FILE"
    exit 1
fi

# Check if test file exists
if [ ! -f "$TEST_FILE" ]; then
    echo "Error: Test file not found: $TEST_FILE"
    exit 1
fi

echo "Running tests for $STEP_NAME..."
echo "Implementation: $ZIKU_FILE"
echo "Test file: $TEST_FILE"

# Run runtest.py
# Using python3 as it is standard
python3 "$MAL_DIR/runtest.py" "$TEST_FILE" -- "$PROJECT_DIR/examples/mal/run" "$PROJECT_DIR/$ZIKU_FILE"
