#!/bin/bash
set -e

echo "Verifying GitHub Issue Templates..."

ERRORS=0

if [ ! -f ".github/ISSUE_TEMPLATE/feature_request.md" ]; then
    echo "❌ Missing feature_request.md"
    ERRORS=$((ERRORS+1))
fi

if [ ! -f ".github/ISSUE_TEMPLATE/bug_report.md" ]; then
    echo "❌ Missing bug_report.md"
    ERRORS=$((ERRORS+1))
fi

if [ ! -f ".github/ISSUE_TEMPLATE/task.md" ]; then
    echo "❌ Missing task.md"
    ERRORS=$((ERRORS+1))
fi

if [ $ERRORS -eq 0 ]; then
    echo "✅ All templates found."
    exit 0
else
    echo "❌ Verification failed with $ERRORS errors."
    exit 1
fi
