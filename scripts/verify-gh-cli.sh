#!/bin/bash
set -e

echo "Verifying GitHub CLI (gh)..."

if ! command -v gh &> /dev/null; then
    echo "❌ gh CLI not found. Please install it: https://cli.github.com/"
    exit 1
fi

echo "gh CLI found: $(gh --version | head -n 1)"

if ! gh auth status &> /dev/null; then
    echo "❌ gh CLI not authenticated. Please run 'gh auth login'."
    exit 1
fi

echo "✅ gh CLI is authenticated."
exit 0
