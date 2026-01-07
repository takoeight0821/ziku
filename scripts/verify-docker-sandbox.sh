#!/bin/bash
set -e

# Colors for output
GREEN='\033[0;32m'
RED='\033[0;31m'
NC='\033[0m' # No Color

pass() {
    echo -e "${GREEN}[PASS]${NC} $1"
}

fail() {
    echo -e "${RED}[FAIL]${NC} $1"
    exit 1
}

echo "Verifying Docker Sandbox Environment..."

# 1. Verify OS
if grep -q "Ubuntu" /etc/os-release; then
    pass "OS is Ubuntu"
else
    fail "OS is not Ubuntu"
fi

# 2. Verify User
if id "gemini" &>/dev/null; then
    pass "User 'gemini' exists"
else
    fail "User 'gemini' does not exist"
fi

# 3. Verify Tools
TOOLS=("git" "curl" "wget" "vim" "nano" "gcc" "make")
for tool in "${TOOLS[@]}"; do
    if command -v "$tool" &>/dev/null; then
        pass "Tool '$tool' is installed"
    else
        fail "Tool '$tool' is NOT installed"
    fi
done

# 4. Verify Elan/Lean
if command -v elan &>/dev/null; then
    pass "elan is installed"
else
    fail "elan is NOT installed"
fi

if command -v lean &>/dev/null; then
    pass "lean is installed"
else
    fail "lean is NOT installed"
fi

echo "All checks passed!"
