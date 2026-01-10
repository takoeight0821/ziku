#!/bin/bash
set -euo pipefail

# Configuration
APP_NAME="renovate-ziku"
REPO_OWNER="takoeight0821"
REPO_NAME="ziku"
HOMEPAGE_URL="https://github.com/${REPO_OWNER}/${REPO_NAME}"

echo "Creating GitHub App: ${APP_NAME}"
echo "This requires GitHub CLI (gh) to be installed and authenticated."
echo

# Check if gh is installed
if ! command -v gh &> /dev/null; then
    echo "Error: GitHub CLI (gh) is not installed."
    echo "Install it from: https://cli.github.com/"
    exit 1
fi

# Check if authenticated
if ! gh auth status &> /dev/null; then
    echo "Error: Not authenticated with GitHub CLI."
    echo "Run: gh auth login"
    exit 1
fi

# Create the GitHub App
echo "Creating GitHub App..."
APP_RESPONSE=$(gh api \
  --method POST \
  /user/apps \
  -f name="${APP_NAME}" \
  -f url="${HOMEPAGE_URL}" \
  -f hook_attributes[active]=false \
  -f public=false \
  -f default_permissions[contents]=write \
  -f default_permissions[pull_requests]=write \
  -f default_permissions[workflows]=write \
  -f default_permissions[metadata]=read \
  2>&1)

if [ $? -ne 0 ]; then
    echo "Error creating GitHub App:"
    echo "$APP_RESPONSE"
    exit 1
fi

APP_ID=$(echo "$APP_RESPONSE" | jq -r '.id')
APP_SLUG=$(echo "$APP_RESPONSE" | jq -r '.slug')
APP_HTML_URL=$(echo "$APP_RESPONSE" | jq -r '.html_url')

echo "✓ GitHub App created successfully!"
echo
echo "App ID: ${APP_ID}"
echo "App Slug: ${APP_SLUG}"
echo "App URL: ${APP_HTML_URL}"
echo

# Generate private key
echo "Generating private key..."
PRIVATE_KEY_RESPONSE=$(gh api \
  --method POST \
  "/app/keys" \
  2>&1)

if [ $? -ne 0 ]; then
    echo "Warning: Could not generate private key via API."
    echo "Please generate it manually at: ${APP_HTML_URL}"
else
    PRIVATE_KEY=$(echo "$PRIVATE_KEY_RESPONSE" | jq -r '.key')
    PRIVATE_KEY_FILE="renovate-app-private-key.pem"
    echo "$PRIVATE_KEY" > "$PRIVATE_KEY_FILE"
    chmod 600 "$PRIVATE_KEY_FILE"
    echo "✓ Private key saved to: ${PRIVATE_KEY_FILE}"
    echo "  Keep this file secure!"
fi

echo
echo "Next steps:"
echo "1. Install the app on your repository:"
echo "   Visit: ${APP_HTML_URL}/installations/new"
echo "   Select: Only select repositories -> ${REPO_OWNER}/${REPO_NAME}"
echo
echo "2. Get the installation ID:"
echo "   After installation, note the ID from the URL"
echo "   (e.g., settings/installations/12345678)"
echo
echo "3. Add secrets to GitHub Actions:"
echo "   - RENOVATE_APP_ID: ${APP_ID}"
echo "   - RENOVATE_APP_PRIVATE_KEY: (contents of ${PRIVATE_KEY_FILE})"
echo
echo "4. (Optional) Manage installation with Terraform"
