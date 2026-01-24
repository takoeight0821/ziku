#!/bin/bash
# Aggregate test results from multiple JSON files and output a summary report.
# Usage: ./scripts/aggregate-test-results.sh [RESULTS_DIR]
# Default RESULTS_DIR is .test-results

set -e

RESULTS_DIR="${1:-.test-results}"

if [ ! -d "$RESULTS_DIR" ]; then
  echo "Error: Results directory '$RESULTS_DIR' not found"
  exit 1
fi

TOTAL_PASSED=0
TOTAL_FAILED=0
FAILED_CATEGORIES=""

echo "=== Test Results ==="
echo ""

for result in "$RESULTS_DIR"/*.json; do
  if [ ! -f "$result" ]; then
    echo "No result files found in $RESULTS_DIR"
    exit 1
  fi

  cat=$(basename "$result" .json)

  # Parse JSON manually (no jq dependency)
  passed=$(grep -o '"passed": *[0-9]*' "$result" | grep -o '[0-9]*')
  failed=$(grep -o '"failed": *[0-9]*' "$result" | grep -o '[0-9]*')

  TOTAL_PASSED=$((TOTAL_PASSED + passed))
  TOTAL_FAILED=$((TOTAL_FAILED + failed))

  status="passed"
  if [ "$failed" -gt 0 ]; then
    FAILED_CATEGORIES="$FAILED_CATEGORIES $cat"
    status="FAILED"
  fi

  printf "%-25s %4d passed, %4d failed  [%s]\n" "$cat:" "$passed" "$failed" "$status"
done

echo ""
echo "========================"
printf "Total: %d passed, %d failed\n" "$TOTAL_PASSED" "$TOTAL_FAILED"

if [ "$TOTAL_FAILED" -gt 0 ]; then
  echo ""
  echo "Failed categories:$FAILED_CATEGORIES"
  exit 1
else
  echo ""
  echo "All tests passed!"
fi
