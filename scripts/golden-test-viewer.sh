#!/bin/bash
# Golden Test Viewer Generator
# Generates an HTML page to browse all golden tests

set -e

SCRIPT_DIR="$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)"
PROJECT_ROOT="$(cd "$SCRIPT_DIR/.." && pwd)"
TEST_DIR="$PROJECT_ROOT/tests/golden"
OUTPUT_FILE="$PROJECT_ROOT/tests/golden-test-viewer.html"

# Start HTML document
cat > "$OUTPUT_FILE" << 'HTMLHEAD'
<!DOCTYPE html>
<html lang="en">
<head>
  <meta charset="UTF-8">
  <meta name="viewport" content="width=device-width, initial-scale=1.0">
  <title>Ziku Golden Test Viewer</title>
  <style>
    :root {
      --bg-primary: #1e1e2e;
      --bg-secondary: #313244;
      --bg-tertiary: #45475a;
      --text-primary: #cdd6f4;
      --text-secondary: #a6adc8;
      --accent: #89b4fa;
      --accent-hover: #b4befe;
      --success: #a6e3a1;
      --error: #f38ba8;
      --border: #585b70;
    }

    * {
      box-sizing: border-box;
      margin: 0;
      padding: 0;
    }

    body {
      font-family: -apple-system, BlinkMacSystemFont, 'Segoe UI', Roboto, Oxygen, Ubuntu, sans-serif;
      background: var(--bg-primary);
      color: var(--text-primary);
      line-height: 1.6;
    }

    header {
      background: var(--bg-secondary);
      padding: 1.5rem 2rem;
      border-bottom: 1px solid var(--border);
      position: sticky;
      top: 0;
      z-index: 100;
    }

    header h1 {
      font-size: 1.5rem;
      margin-bottom: 1rem;
    }

    .controls {
      display: flex;
      gap: 1rem;
      flex-wrap: wrap;
      align-items: center;
    }

    .search-box {
      flex: 1;
      min-width: 200px;
      max-width: 400px;
    }

    .search-box input {
      width: 100%;
      padding: 0.5rem 1rem;
      border: 1px solid var(--border);
      border-radius: 6px;
      background: var(--bg-primary);
      color: var(--text-primary);
      font-size: 0.9rem;
    }

    .search-box input:focus {
      outline: none;
      border-color: var(--accent);
    }

    .filter-group {
      display: flex;
      gap: 0.5rem;
      flex-wrap: wrap;
      align-items: center;
    }

    .filter-label {
      font-size: 0.8rem;
      color: var(--text-secondary);
    }

    .filter-btn {
      padding: 0.4rem 0.8rem;
      border: 1px solid var(--border);
      border-radius: 20px;
      background: var(--bg-tertiary);
      color: var(--text-secondary);
      cursor: pointer;
      font-size: 0.85rem;
      transition: all 0.2s;
    }

    .filter-btn:hover {
      border-color: var(--accent);
      color: var(--text-primary);
    }

    .filter-btn.active {
      background: var(--accent);
      color: var(--bg-primary);
      border-color: var(--accent);
    }

    .filter-btn.success-filter.active {
      background: var(--success);
    }

    .filter-btn.error-filter.active {
      background: var(--error);
    }

    .stats {
      color: var(--text-secondary);
      font-size: 0.85rem;
    }

    main {
      padding: 2rem;
      max-width: 1600px;
      margin: 0 auto;
    }

    .category-section {
      margin-bottom: 3rem;
    }

    .category-header {
      display: flex;
      align-items: center;
      gap: 1rem;
      margin-bottom: 1rem;
      padding-bottom: 0.5rem;
      border-bottom: 2px solid var(--accent);
    }

    .category-header h2 {
      font-size: 1.2rem;
      color: var(--accent);
    }

    .category-count {
      background: var(--bg-tertiary);
      padding: 0.2rem 0.6rem;
      border-radius: 12px;
      font-size: 0.8rem;
      color: var(--text-secondary);
    }

    .subcategory-header {
      font-size: 0.9rem;
      color: var(--text-secondary);
      margin: 1rem 0 0.5rem 0;
      padding-left: 0.5rem;
      border-left: 3px solid var(--border);
    }

    .subcategory-header.success-header {
      border-color: var(--success);
      color: var(--success);
    }

    .subcategory-header.error-header {
      border-color: var(--error);
      color: var(--error);
    }

    .test-grid {
      display: grid;
      gap: 1rem;
    }

    .test-card {
      background: var(--bg-secondary);
      border-radius: 8px;
      border: 1px solid var(--border);
      overflow: hidden;
      transition: border-color 0.2s;
    }

    .test-card:hover {
      border-color: var(--accent);
    }

    .test-card.hidden {
      display: none;
    }

    .test-card.error-test {
      border-left: 3px solid var(--error);
    }

    .test-card.success-test {
      border-left: 3px solid var(--success);
    }

    .test-header {
      display: flex;
      justify-content: space-between;
      align-items: center;
      padding: 0.75rem 1rem;
      background: var(--bg-tertiary);
      cursor: pointer;
    }

    .test-name {
      font-weight: 500;
      font-family: 'SF Mono', 'Fira Code', monospace;
      font-size: 0.9rem;
    }

    .test-badge {
      font-size: 0.7rem;
      padding: 0.15rem 0.4rem;
      border-radius: 4px;
      margin-left: 0.5rem;
    }

    .test-badge.success {
      background: var(--success);
      color: var(--bg-primary);
    }

    .test-badge.error {
      background: var(--error);
      color: var(--bg-primary);
    }

    .test-toggle {
      color: var(--text-secondary);
      font-size: 0.8rem;
    }

    .test-content {
      display: none;
      padding: 1rem;
    }

    .test-card.expanded .test-content {
      display: block;
    }

    .test-card.expanded .test-toggle::after {
      content: '▲';
    }

    .test-card:not(.expanded) .test-toggle::after {
      content: '▼';
    }

    .code-panels {
      display: grid;
      grid-template-columns: 1fr 1fr;
      gap: 1rem;
    }

    @media (max-width: 800px) {
      .code-panels {
        grid-template-columns: 1fr;
      }
    }

    .code-panel {
      background: var(--bg-primary);
      border-radius: 6px;
      overflow: hidden;
    }

    .code-panel-header {
      padding: 0.5rem 0.75rem;
      background: var(--bg-tertiary);
      font-size: 0.75rem;
      color: var(--text-secondary);
      text-transform: uppercase;
      letter-spacing: 0.05em;
    }

    .code-panel pre {
      padding: 1rem;
      margin: 0;
      overflow-x: auto;
      font-family: 'SF Mono', 'Fira Code', monospace;
      font-size: 0.85rem;
      line-height: 1.5;
      white-space: pre-wrap;
      word-break: break-word;
    }

    .input-panel pre {
      color: #f9e2af;
    }

    .output-panel pre {
      color: var(--success);
    }

    .error-test .output-panel pre {
      color: var(--error);
    }

    .expand-all-btn {
      padding: 0.4rem 0.8rem;
      border: 1px solid var(--border);
      border-radius: 6px;
      background: var(--bg-tertiary);
      color: var(--text-secondary);
      cursor: pointer;
      font-size: 0.85rem;
    }

    .expand-all-btn:hover {
      border-color: var(--accent);
      color: var(--text-primary);
    }

    .no-results {
      text-align: center;
      padding: 3rem;
      color: var(--text-secondary);
    }

    .refresh-controls {
      display: flex;
      align-items: center;
      gap: 0.5rem;
    }

    .refresh-btn {
      padding: 0.4rem 0.8rem;
      border: 1px solid var(--border);
      border-radius: 6px;
      background: var(--bg-tertiary);
      color: var(--text-secondary);
      cursor: pointer;
      font-size: 0.85rem;
    }

    .refresh-btn:hover {
      border-color: var(--accent);
      color: var(--text-primary);
    }

    .refresh-btn.active {
      background: var(--accent);
      color: var(--bg-primary);
      border-color: var(--accent);
    }

    .refresh-btn.spinning .refresh-icon {
      animation: spin 1s linear infinite;
    }

    @keyframes spin {
      from { transform: rotate(0deg); }
      to { transform: rotate(360deg); }
    }

    .refresh-icon {
      display: inline-block;
    }

    .last-updated {
      font-size: 0.75rem;
      color: var(--text-secondary);
    }

    .auto-refresh-label {
      font-size: 0.8rem;
      color: var(--text-secondary);
      display: flex;
      align-items: center;
      gap: 0.3rem;
      cursor: pointer;
    }

    .auto-refresh-label input {
      cursor: pointer;
    }
  </style>
</head>
<body>
  <header>
    <h1>Ziku Golden Test Viewer</h1>
    <div class="controls">
      <div class="search-box">
        <input type="text" id="search" placeholder="Search tests...">
      </div>
      <div class="filter-group">
        <span class="filter-label">Category:</span>
        <button class="filter-btn active" data-category="all">All</button>
HTMLHEAD

# Collect categories (excluding scheme which uses ir-eval sources)
categories=$(find "$TEST_DIR" -mindepth 1 -maxdepth 1 -type d ! -name "scheme" -exec basename {} \; | sort)

# Add category filter buttons
for category in $categories; do
  success_count=$(find "$TEST_DIR/$category/success" -name "*.ziku" 2>/dev/null | wc -l | tr -d ' ')
  error_count=$(find "$TEST_DIR/$category/error" -name "*.ziku" 2>/dev/null | wc -l | tr -d ' ')
  total=$((success_count + error_count))
  if [ "$total" -gt 0 ]; then
    echo "        <button class=\"filter-btn\" data-category=\"$category\">$category ($total)</button>" >> "$OUTPUT_FILE"
  fi
done

cat >> "$OUTPUT_FILE" << 'HTMLMID1'
      </div>
      <div class="filter-group">
        <span class="filter-label">Type:</span>
        <button class="filter-btn type-filter active" data-type="all">All</button>
        <button class="filter-btn type-filter success-filter" data-type="success">Success</button>
        <button class="filter-btn type-filter error-filter" data-type="error">Error</button>
      </div>
      <button class="expand-all-btn" id="expandAll">Expand All</button>
      <div class="refresh-controls">
        <button class="refresh-btn" id="refreshBtn" title="Refresh"><span class="refresh-icon">↻</span></button>
        <label class="auto-refresh-label">
          <input type="checkbox" id="autoRefresh"> Auto (3s)
        </label>
        <span class="last-updated" id="lastUpdated"></span>
      </div>
      <div class="stats" id="stats"></div>
    </div>
  </header>
  <main id="mainContent">
HTMLMID1

# Function to escape HTML
escape_html() {
  sed 's/&/\&amp;/g; s/</\&lt;/g; s/>/\&gt;/g; s/"/\&quot;/g'
}

# Generate test cards for each category
for category in $categories; do
  success_files=$(find "$TEST_DIR/$category/success" -name "*.ziku" 2>/dev/null | sort)
  error_files=$(find "$TEST_DIR/$category/error" -name "*.ziku" 2>/dev/null | sort)

  if [ -n "$success_files" ]; then
    success_count=$(echo "$success_files" | wc -l | tr -d ' ')
  else
    success_count=0
  fi
  if [ -n "$error_files" ]; then
    error_count=$(echo "$error_files" | wc -l | tr -d ' ')
  else
    error_count=0
  fi
  total=$((success_count + error_count))

  if [ "$total" -eq 0 ]; then
    continue
  fi

  cat >> "$OUTPUT_FILE" << CATHEAD
    <section class="category-section" data-category="$category">
      <div class="category-header">
        <h2>$category</h2>
        <span class="category-count">$total tests ($success_count success, $error_count error)</span>
      </div>
      <div class="test-grid">
CATHEAD

  # Success tests
  if [ -n "$success_files" ]; then
    for ziku_file in $success_files; do
      test_name=$(basename "$ziku_file" .ziku)
      golden_file="${ziku_file%.ziku}.golden"

      input_content=$(cat "$ziku_file" | escape_html)

      if [ -f "$golden_file" ]; then
        output_content=$(cat "$golden_file" | escape_html)
      else
        output_content="(golden file not found)"
      fi

      cat >> "$OUTPUT_FILE" << TESTCARD
        <div class="test-card success-test" data-name="$test_name" data-category="$category" data-type="success">
          <div class="test-header" onclick="toggleCard(this.parentElement)">
            <span class="test-name">$test_name<span class="test-badge success">success</span></span>
            <span class="test-toggle"></span>
          </div>
          <div class="test-content">
            <div class="code-panels">
              <div class="code-panel input-panel">
                <div class="code-panel-header">Input (.ziku)</div>
                <pre>$input_content</pre>
              </div>
              <div class="code-panel output-panel">
                <div class="code-panel-header">Expected (.golden)</div>
                <pre>$output_content</pre>
              </div>
            </div>
          </div>
        </div>
TESTCARD
    done
  fi

  # Error tests
  if [ -n "$error_files" ]; then
    for ziku_file in $error_files; do
      test_name=$(basename "$ziku_file" .ziku)
      golden_file="${ziku_file%.ziku}.golden"

      input_content=$(cat "$ziku_file" | escape_html)

      if [ -f "$golden_file" ]; then
        output_content=$(cat "$golden_file" | escape_html)
      else
        output_content="(golden file not found)"
      fi

      cat >> "$OUTPUT_FILE" << TESTCARD
        <div class="test-card error-test" data-name="$test_name" data-category="$category" data-type="error">
          <div class="test-header" onclick="toggleCard(this.parentElement)">
            <span class="test-name">$test_name<span class="test-badge error">error</span></span>
            <span class="test-toggle"></span>
          </div>
          <div class="test-content">
            <div class="code-panels">
              <div class="code-panel input-panel">
                <div class="code-panel-header">Input (.ziku)</div>
                <pre>$input_content</pre>
              </div>
              <div class="code-panel output-panel">
                <div class="code-panel-header">Expected Error (.golden)</div>
                <pre>$output_content</pre>
              </div>
            </div>
          </div>
        </div>
TESTCARD
    done
  fi

  echo "      </div>" >> "$OUTPUT_FILE"
  echo "    </section>" >> "$OUTPUT_FILE"
done

# Add generation timestamp
GENERATED_AT=$(date '+%Y-%m-%d %H:%M:%S')

# Close HTML with JavaScript
cat >> "$OUTPUT_FILE" << HTMLFOOT
    <div class="no-results" id="noResults" style="display: none;">
      No tests match your search.
    </div>
  </main>

  <script>
    const GENERATED_AT = '$GENERATED_AT';
    const searchInput = document.getElementById('search');
    const categoryBtns = document.querySelectorAll('.filter-btn:not(.type-filter)');
    const typeBtns = document.querySelectorAll('.type-filter');
    let testCards = document.querySelectorAll('.test-card');
    let categorySections = document.querySelectorAll('.category-section');
    const statsEl = document.getElementById('stats');
    const noResultsEl = document.getElementById('noResults');
    const expandAllBtn = document.getElementById('expandAll');
    const refreshBtn = document.getElementById('refreshBtn');
    const autoRefreshCheckbox = document.getElementById('autoRefresh');
    const lastUpdatedEl = document.getElementById('lastUpdated');
    const mainContent = document.getElementById('mainContent');

    let currentCategory = 'all';
    let currentType = 'all';
    let allExpanded = false;
    let autoRefreshInterval = null;
    let expandedCards = new Set();

    function toggleCard(card) {
      card.classList.toggle('expanded');
      const name = card.dataset.name + '-' + card.dataset.category;
      if (card.classList.contains('expanded')) {
        expandedCards.add(name);
      } else {
        expandedCards.delete(name);
      }
    }

    function updateStats() {
      testCards = document.querySelectorAll('.test-card');
      const visible = document.querySelectorAll('.test-card:not(.hidden)').length;
      const total = testCards.length;
      const successCount = document.querySelectorAll('.test-card.success-test:not(.hidden)').length;
      const errorCount = document.querySelectorAll('.test-card.error-test:not(.hidden)').length;
      statsEl.textContent = \`Showing \${visible} of \${total} tests (\${successCount} success, \${errorCount} error)\`;
      noResultsEl.style.display = visible === 0 ? 'block' : 'none';
    }

    function filterTests() {
      testCards = document.querySelectorAll('.test-card');
      categorySections = document.querySelectorAll('.category-section');
      const searchTerm = searchInput.value.toLowerCase();

      testCards.forEach(card => {
        const name = card.dataset.name.toLowerCase();
        const category = card.dataset.category;
        const type = card.dataset.type;
        const matchesSearch = name.includes(searchTerm);
        const matchesCategory = currentCategory === 'all' || category === currentCategory;
        const matchesType = currentType === 'all' || type === currentType;

        card.classList.toggle('hidden', !(matchesSearch && matchesCategory && matchesType));
      });

      categorySections.forEach(section => {
        const category = section.dataset.category;
        const hasVisibleCards = section.querySelectorAll('.test-card:not(.hidden)').length > 0;
        const matchesCategory = currentCategory === 'all' || category === currentCategory;
        section.style.display = (matchesCategory && hasVisibleCards) ? 'block' : 'none';
      });

      updateStats();
    }

    function updateLastUpdated() {
      const now = new Date();
      lastUpdatedEl.textContent = 'Updated: ' + now.toLocaleTimeString();
    }

    async function refreshContent() {
      refreshBtn.classList.add('spinning');
      try {
        const response = await fetch(window.location.href + '?t=' + Date.now());
        const html = await response.text();
        const parser = new DOMParser();
        const doc = parser.parseFromString(html, 'text/html');
        const newMain = doc.getElementById('mainContent');
        if (newMain) {
          mainContent.innerHTML = newMain.innerHTML;
          // Re-query elements after DOM update
          testCards = document.querySelectorAll('.test-card');
          categorySections = document.querySelectorAll('.category-section');
          // Restore expanded state
          testCards.forEach(card => {
            const name = card.dataset.name + '-' + card.dataset.category;
            if (expandedCards.has(name)) {
              card.classList.add('expanded');
            }
          });
          filterTests();
          updateLastUpdated();
        }
      } catch (e) {
        console.error('Refresh failed:', e);
      }
      refreshBtn.classList.remove('spinning');
    }

    searchInput.addEventListener('input', filterTests);

    categoryBtns.forEach(btn => {
      btn.addEventListener('click', () => {
        categoryBtns.forEach(b => b.classList.remove('active'));
        btn.classList.add('active');
        currentCategory = btn.dataset.category;
        filterTests();
      });
    });

    typeBtns.forEach(btn => {
      btn.addEventListener('click', () => {
        typeBtns.forEach(b => b.classList.remove('active'));
        btn.classList.add('active');
        currentType = btn.dataset.type;
        filterTests();
      });
    });

    expandAllBtn.addEventListener('click', () => {
      allExpanded = !allExpanded;
      testCards = document.querySelectorAll('.test-card');
      testCards.forEach(card => {
        if (!card.classList.contains('hidden')) {
          card.classList.toggle('expanded', allExpanded);
          const name = card.dataset.name + '-' + card.dataset.category;
          if (allExpanded) {
            expandedCards.add(name);
          } else {
            expandedCards.delete(name);
          }
        }
      });
      expandAllBtn.textContent = allExpanded ? 'Collapse All' : 'Expand All';
    });

    refreshBtn.addEventListener('click', refreshContent);

    autoRefreshCheckbox.addEventListener('change', () => {
      if (autoRefreshCheckbox.checked) {
        refreshBtn.classList.add('active');
        autoRefreshInterval = setInterval(refreshContent, 3000);
      } else {
        refreshBtn.classList.remove('active');
        if (autoRefreshInterval) {
          clearInterval(autoRefreshInterval);
          autoRefreshInterval = null;
        }
      }
    });

    // Initial setup
    updateStats();
    lastUpdatedEl.textContent = 'Generated: ' + GENERATED_AT;
  </script>
</body>
</html>
HTMLFOOT

echo "Generated: $OUTPUT_FILE"
echo "Open in browser: file://$OUTPUT_FILE"
