#!/bin/bash
set -e

echo "Verifying Documentation and Deprecation..."

if [ ! -f "docs/cdd-workflow.md" ]; then
    echo "❌ Missing docs/cdd-workflow.md"
    exit 1
fi

if ! grep -q "GitHub-First development process" README.md; then
    echo "❌ README.md not updated with CDD workflow link"
    exit 1
fi

if [ ! -f "conductor/DEPRECATED.md" ]; then
    echo "❌ Missing conductor/DEPRECATED.md"
    exit 1
fi

echo "✅ Documentation verification passed."
