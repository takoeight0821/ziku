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

    .category-filters {
      display: flex;
      gap: 0.5rem;
      flex-wrap: wrap;
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
  </style>
</head>
<body>
  <header>
    <h1>Ziku Golden Test Viewer</h1>
    <div class="controls">
      <div class="search-box">
        <input type="text" id="search" placeholder="Search tests...">
      </div>
      <div class="category-filters">
        <button class="filter-btn active" data-category="all">All</button>
HTMLHEAD

# Collect categories
categories=$(find "$TEST_DIR" -mindepth 1 -maxdepth 1 -type d -exec basename {} \; | sort)

# Add category filter buttons
for category in $categories; do
  count=$(find "$TEST_DIR/$category" -name "*.ziku" 2>/dev/null | wc -l | tr -d ' ')
  if [ "$count" -gt 0 ]; then
    echo "        <button class=\"filter-btn\" data-category=\"$category\">$category ($count)</button>" >> "$OUTPUT_FILE"
  fi
done

cat >> "$OUTPUT_FILE" << 'HTMLMID'
      </div>
      <button class="expand-all-btn" id="expandAll">Expand All</button>
      <div class="stats" id="stats"></div>
    </div>
  </header>
  <main>
HTMLMID

# Function to escape HTML
escape_html() {
  sed 's/&/\&amp;/g; s/</\&lt;/g; s/>/\&gt;/g; s/"/\&quot;/g'
}

# Generate test cards for each category
for category in $categories; do
  ziku_files=$(find "$TEST_DIR/$category" -name "*.ziku" 2>/dev/null | sort)

  if [ -z "$ziku_files" ]; then
    continue
  fi

  count=$(echo "$ziku_files" | wc -l | tr -d ' ')

  cat >> "$OUTPUT_FILE" << CATHEAD
    <section class="category-section" data-category="$category">
      <div class="category-header">
        <h2>$category</h2>
        <span class="category-count">$count tests</span>
      </div>
      <div class="test-grid">
CATHEAD

  for ziku_file in $ziku_files; do
    test_name=$(basename "$ziku_file" .ziku)
    golden_file="${ziku_file%.ziku}.golden"

    # Read and escape file contents
    input_content=$(cat "$ziku_file" | escape_html)

    if [ -f "$golden_file" ]; then
      output_content=$(cat "$golden_file" | escape_html)
    else
      output_content="(golden file not found)"
    fi

    cat >> "$OUTPUT_FILE" << TESTCARD
        <div class="test-card" data-name="$test_name" data-category="$category">
          <div class="test-header" onclick="toggleCard(this.parentElement)">
            <span class="test-name">$test_name</span>
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

  echo "      </div>" >> "$OUTPUT_FILE"
  echo "    </section>" >> "$OUTPUT_FILE"
done

# Close HTML with JavaScript
cat >> "$OUTPUT_FILE" << 'HTMLFOOT'
    <div class="no-results" id="noResults" style="display: none;">
      No tests match your search.
    </div>
  </main>

  <script>
    const searchInput = document.getElementById('search');
    const filterBtns = document.querySelectorAll('.filter-btn');
    const testCards = document.querySelectorAll('.test-card');
    const categorySections = document.querySelectorAll('.category-section');
    const statsEl = document.getElementById('stats');
    const noResultsEl = document.getElementById('noResults');
    const expandAllBtn = document.getElementById('expandAll');

    let currentCategory = 'all';
    let allExpanded = false;

    function toggleCard(card) {
      card.classList.toggle('expanded');
    }

    function updateStats() {
      const visible = document.querySelectorAll('.test-card:not(.hidden)').length;
      const total = testCards.length;
      statsEl.textContent = `Showing ${visible} of ${total} tests`;
      noResultsEl.style.display = visible === 0 ? 'block' : 'none';
    }

    function filterTests() {
      const searchTerm = searchInput.value.toLowerCase();

      testCards.forEach(card => {
        const name = card.dataset.name.toLowerCase();
        const category = card.dataset.category;
        const matchesSearch = name.includes(searchTerm);
        const matchesCategory = currentCategory === 'all' || category === currentCategory;

        card.classList.toggle('hidden', !(matchesSearch && matchesCategory));
      });

      categorySections.forEach(section => {
        const category = section.dataset.category;
        const hasVisibleCards = section.querySelectorAll('.test-card:not(.hidden)').length > 0;
        const matchesCategory = currentCategory === 'all' || category === currentCategory;
        section.style.display = (matchesCategory && hasVisibleCards) ? 'block' : 'none';
      });

      updateStats();
    }

    searchInput.addEventListener('input', filterTests);

    filterBtns.forEach(btn => {
      btn.addEventListener('click', () => {
        filterBtns.forEach(b => b.classList.remove('active'));
        btn.classList.add('active');
        currentCategory = btn.dataset.category;
        filterTests();
      });
    });

    expandAllBtn.addEventListener('click', () => {
      allExpanded = !allExpanded;
      testCards.forEach(card => {
        if (!card.classList.contains('hidden')) {
          card.classList.toggle('expanded', allExpanded);
        }
      });
      expandAllBtn.textContent = allExpanded ? 'Collapse All' : 'Expand All';
    });

    // Initial stats
    updateStats();
  </script>
</body>
</html>
HTMLFOOT

echo "Generated: $OUTPUT_FILE"
echo "Open in browser: file://$OUTPUT_FILE"
