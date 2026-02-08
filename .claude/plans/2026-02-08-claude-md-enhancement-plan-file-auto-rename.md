# CLAUDE.md Enhancement + Plan File Auto-Rename

**Date**: 2026-02-08
**Status**: Ready for implementation

---

## Context

Two related improvements to developer experience and documentation:

### Problem 1: CLAUDE.md Quality Gaps (Current Score: 82/100)

While the current CLAUDE.md is well-structured, it's missing critical information that causes repeated questions and mistakes:
- Missing commands (e.g., `mise run docker:run` for quick testing)
- No module navigation guide (12 core modules, hard to locate)
- Critical gotchas from MEMORY.md not documented (hygienic names, golden test updates, ElabM patterns)
- Golden test workflow incomplete (`.golden` file creation not explained)

These gaps lead to inefficiency when working with the codebase.

### Problem 2: Plan File Naming Inconsistency

Plan files are auto-generated with random names (`wobbly-crunching-candy.md`, `snoopy-wandering-fairy.md`), but the project convention is date-based: `YYYY-MM-DD-descriptive-title.md`.

Current state:
- 16 plan files total
- 3 files violate convention (random names)
- All plans contain date in first line: `# 2026-02-08: <title>`
- Manual renaming is tedious and often forgotten

**User's proposal**: Automate renaming using Claude Code's hook system when plan mode exits.

---

## Solution Overview

### Task 1: CLAUDE.md Updates (~50 lines)
Add 4 targeted sections with genuinely useful, non-obvious information:
1. Missing `docker:run` command
2. Key Modules navigation guide
3. Critical Gotchas from MEMORY.md
4. Golden Test creation workflow

### Task 2: Plan File Naming Warning Hook
Create a `Stop` hook that:
- Detects plan files with random names (not following `YYYY-MM-DD-` convention)
- Warns the user about files that should be renamed
- Suggests the correct naming format based on date/title extraction
- Does NOT automatically rename (safer, user retains control)

**Why warning-only?**
- Safer: No risk of data loss or incorrect renames
- User control: User decides when and how to rename
- Simpler: No edge case handling for overwrites, non-ASCII titles, etc.
- Less intrusive: Only notifies when convention is violated

**Why Stop hook?** Claude Code has no `ExitPlanMode` hook. The `Stop` hook fires when Claude finishes responding, allowing us to detect plan files.

---

## Implementation Plan

### Phase 1: CLAUDE.md Updates (Low Risk, High Impact)

#### Change 1: Add Missing Command to Build Commands
**File**: `CLAUDE.md` (line 26)
**Action**: Insert after `mise run docker:infer` line

```markdown
mise run docker:run <phase> <expr-or-file>  # Quick test of expression or file
```

**Verification**: Run `mise run docker:run parse 'let x = 1 in x'`

#### Change 2: Add Key Modules Section to Architecture
**File**: `CLAUDE.md` (after line 57)
**Action**: Insert new subsection after "Key points"

```markdown
### Key Modules

**Core pipeline** (in execution order):
- `Lexer.lean` - Tokenization, forbids `#` in user identifiers
- `Parser.lean` - Hand-written parser (Parsec API issues)
- `Elaborate.lean` - Copattern desugaring to records/lambdas
  - Uses `ElabM := StateT Nat (Except ElaborateError)` for fresh names
  - Public API: `elaborateAll` wraps with `.run' 0`
- `Infer.lean` - Hindley-Milner type inference with let-polymorphism
  - Calls `(elaborate pos clauses).run' 0` for codata elaboration
- `Translate.lean` - Surface → sequent calculus IR
- `Backend/Scheme.lean` - Code generation (`#` → `_hash_`)

**Supporting modules**:
- `FreshName.lean` - Hygienic name constants (`#` prefix system)
  - All compiler-generated names: `#α0`, `#wild`, `#lit_int_42`
  - Central constants: `wildCon`, `varCon`, `litIntPrefix`
- `Syntax.lean` - AST definitions
- `Type.lean` - Type representation
- `Import.lean` - Module system resolution
```

**Verification**: Check all referenced files exist

#### Change 3: Expand Hints Section with Gotchas
**File**: `CLAUDE.md` (lines 107-110)
**Action**: Replace existing Hints with expanded version

```markdown
## Hints

### General
- `rm` is denied for safety, use `trash` command instead
- If you want to try simpler case, you should add it as golden test
- If you write a plan, please add the date at the top of the file

### Type System (Infer.lean)
- **Variable numbering shifts**: Adding `freshTyVar` calls shifts `_tN` numbering in golden tests. Always update golden files after constraint generation changes.
- **ElabM pattern**: `Elaborate.lean` returns `ElabM Expr`. Callers (e.g., `Infer.lean`) must use `(elaborate pos clauses).run' 0`.

### Hygienic Names (FreshName.lean)
- **`#` prefix system**: All compiler-generated variables use `#` prefix (e.g., `#α0`, `#wild`, `#lit_int_42`)
- The `#` char is invalid in user identifiers but handled by Scheme backend's `mangleIdent` (`#` → `_hash_`)
- Import `Ziku.FreshName` for constants like `wildCon`, `varCon`, `litIntPrefix`

### Docker/Build
- Docker rebuilds on every `mise run docker:*` (depends on `docker:build`)
- Tests copy from host `tests/` dir, so golden file changes need image rebuild
- Build is cached if only test files change (Docker layer optimization)
```

**Source**: All information from `MEMORY.md` (verified learnings)

#### Change 4: Add Golden Test Workflow
**File**: `CLAUDE.md` (after line 91)
**Action**: Insert new subsection after "Available categories"

```markdown
### Golden Test Workflow

**Creating new tests**:
1. Write `.ziku` file in appropriate category (e.g., `tests/golden/infer/success/my_test.ziku`)
2. Run via Docker to generate output: `mise run docker:run <phase> tests/golden/.../my_test.ziku`
3. Copy expected output to `.golden` file: `tests/golden/infer/success/my_test.golden`
4. Run category tests: `mise run docker:test:category infer`

**Moving tests**:
- Moving between `error/` and `success/` requires creating new `.golden` files
- Golden files are not automatically regenerated on move
```

**Verification**: Test workflow with a new golden test

#### Total Impact
- **Lines added**: ~50 net lines
- **Quality score target**: 90+/100
- **Risk**: Low (documentation only, no code changes)

---

### Phase 2: Plan File Naming Warning Hook (Low Complexity, Safe)

#### Component 1: Hook Script
**File**: `.claude/hooks/warn-plan-naming.sh` (create new)
**Permissions**: `chmod +x`

```bash
#!/bin/bash
# Hook: Warn about randomly-named plan files that violate naming convention
# Triggered by: Stop hook (when Claude finishes responding)
# Convention: YYYY-MM-DD-descriptive-title.md

# Read JSON input (Stop hook provides session context)
input=$(cat)

# Use CLAUDE_PROJECT_DIR if available, fallback to current dir
PLANS_DIR="${CLAUDE_PROJECT_DIR:-.}/.claude/plans"

# Exit silently if plans directory doesn't exist
[ -d "$PLANS_DIR" ] || exit 0

# Check for files with random names (not starting with YYYY-MM-DD)
violations=()
while IFS= read -r file; do
    basename=$(basename "$file" .md)

    # Skip if already date-named (starts with YYYY-MM-DD)
    if [[ "$basename" =~ ^[0-9]{4}-[0-9]{2}-[0-9]{2}- ]]; then
        continue
    fi

    # Skip if doesn't match random pattern (less than 3 word-segments)
    word_count=$(echo "$basename" | tr '-' '\n' | wc -l)
    if [ "$word_count" -lt 3 ]; then
        continue
    fi

    violations+=("$basename")
done < <(find "$PLANS_DIR" -name "*.md" -type f 2>/dev/null)

# Warn if violations found
if [ ${#violations[@]} -gt 0 ]; then
    echo "" >&2
    echo "⚠️  Plan file naming convention violation:" >&2
    echo "" >&2
    for name in "${violations[@]}"; do
        echo "  - $name.md" >&2
    done
    echo "" >&2
    echo "Convention: YYYY-MM-DD-descriptive-title.md" >&2
    echo "Please rename these files to follow the project convention." >&2
    echo "" >&2
fi

exit 0
```

**Key Design Decisions**:
- **Warning only**: No automatic renaming (safer)
- **Simple detection**: Checks all plans, not just recent ones
- **Clear output**: Lists all violations at once
- **Non-blocking**: Always exits 0 (never blocks Claude)
- **Minimal logic**: No complex parsing, just pattern matching

#### Component 2: Hook Registration
**File**: `.claude/settings.json`
**Action**: Add `hooks` section (currently doesn't exist)

```json
{
  "permissions": {
    "allow": [
      "Bash(lake build)",
      "Bash(lake test*)",
      "Bash(docker compose build:*)",
      "Bash(docker compose run:*)",
      "Bash(mise run docker:build-check:*)",
      "Bash(mise run docker:test:*)",
      "Bash(mise run docker:test:category:*)",
      "Bash(mise run docker:build:*)",
      "Bash(mise run docker:run:*)"
    ],
    "ask": [
      "Bash(git commit:*)"
    ],
    "deny": [
      "Bash(rm:*)"
    ]
  },
  "plansDirectory": "./.claude/plans",
  "hooks": {
    "Stop": [
      {
        "hooks": [
          {
            "type": "command",
            "command": "$CLAUDE_PROJECT_DIR/.claude/hooks/warn-plan-naming.sh",
            "async": false
          }
        ]
      }
    ]
  }
}
```

**Changes**:
- Add `hooks` object with `Stop` event
- Hook runs synchronously (fast operation, <10ms)
- Uses `$CLAUDE_PROJECT_DIR` for portability

#### Current Violations
Files that will trigger warnings:
- `wobbly-crunching-candy.md` (already renamed to `2026-02-08-combined-stream-zipwith-fib-codata-example.md`)
- `snoopy-wandering-fairy.md` (this plan file)
- `dynamic-stargazing-snowflake.md` (Japanese title)
- `shiny-cuddling-eagle.md`

---

## Implementation Sequence

**Recommended**: Sequential implementation (test each phase separately)

### Phase 1: CLAUDE.md Updates (30 minutes)
1. Make all 4 changes to CLAUDE.md
2. Verify commands work: `mise run docker:run parse 'let x = 1 in x'`
3. Check file references exist (Lexer.lean, FreshName.lean, etc.)
4. Commit: `docs: enhance CLAUDE.md with commands, modules, and gotchas`

### Phase 2: Hook Implementation (15 minutes)
1. Create `.claude/hooks/warn-plan-naming.sh` with executable permissions
2. Update `.claude/settings.json` with hook registration
3. Test manually:
   ```bash
   CLAUDE_PROJECT_DIR=/Users/y002168/ghq/github.com/takoeight0821/ziku \
     .claude/hooks/warn-plan-naming.sh
   ```
4. Verify warning output lists violations
5. Test Stop hook integration (respond in conversation, check warning appears)
6. Commit: `feat: add plan file naming convention warning hook`

**Why sequential?** Lower risk, easier debugging, independent validation.

---

## Files Modified/Created

### CLAUDE.md Updates
- **Modified**: `CLAUDE.md`
  - Line 26: Add `docker:run` command (1 line)
  - After line 57: Add Key Modules section (22 lines)
  - Lines 107-110: Expand Hints section (19 lines, net +15)
  - After line 91: Add Golden Test Workflow (12 lines)

### Plan Naming Warning Hook
- **Created**: `.claude/hooks/warn-plan-naming.sh` (40 lines)
  - Make executable: `chmod +x .claude/hooks/warn-plan-naming.sh`
- **Modified**: `.claude/settings.json`
  - Add `hooks` section with Stop hook registration

---

## Verification

### CLAUDE.md Verification
1. **Syntax check**: Read CLAUDE.md in new session, verify formatting
2. **Command verification**:
   ```bash
   mise run docker:run parse 'let x = 1 in x'
   mise run docker:test:category parser
   ```
3. **File reference verification**: Confirm all mentioned modules exist
4. **Readability test**: Can Claude quickly find gotchas in new session?

### Hook Verification
1. **Script validation**:
   ```bash
   shellcheck .claude/hooks/warn-plan-naming.sh
   ```
2. **Manual test**:
   ```bash
   CLAUDE_PROJECT_DIR=/Users/y002168/ghq/github.com/takoeight0821/ziku \
     .claude/hooks/warn-plan-naming.sh
   ```
   Expected output:
   ```
   ⚠️  Plan file naming convention violation:

     - snoopy-wandering-fairy.md
     - dynamic-stargazing-snowflake.md
     - shiny-cuddling-eagle.md

   Convention: YYYY-MM-DD-descriptive-title.md
   Please rename these files to follow the project convention.
   ```
3. **Edge case tests**:
   - Already-renamed files (should skip silently)
   - Short filenames (should skip if <3 segments)
   - Empty plans directory (should exit silently)
4. **Integration test**: Send a message in conversation, verify warning appears in output
5. **Performance test**: Hook should complete in <10ms (instant)

---

## Success Criteria

### CLAUDE.md Updates ✓
- Quality score improves from 82 → 90+
- All referenced modules/commands exist and work
- New sections integrate smoothly (no style breaks)
- Claude can quickly locate information in new session

### Plan Naming Warning Hook ✓
- All random-named files detected and listed
- Date-based files remain untouched (no false positives)
- Warning only appears when violations exist
- Clear, actionable warning message
- Hook runs instantly (<10ms overhead)
- Non-blocking: always exits successfully

---

## Risks & Mitigations

### Low Risk
- **CLAUDE.md updates**: Documentation only, no code changes
- **Mitigation**: All info from verified sources (MEMORY.md, existing files)

### Very Low Risk
- **Hook triggers on every response**: Stop hook fires frequently
- **Mitigation**: Instant execution (<10ms), only warns if violations exist

### Very Low Risk
- **Hook system changes**: Claude Code updates could break hooks
- **Mitigation**: Simple script with no complex logic, follows existing patterns

---

## Future Enhancements

### CLAUDE.md
- Add "Common Pitfalls" from future MEMORY.md learnings
- Create quality checklist for updates

### Plan Naming Warning Hook
- Add suggested rename commands in warning output
- Support custom naming conventions via settings
- Integrate with plan index generation
