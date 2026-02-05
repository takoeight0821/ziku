# Fix Import Circular Test Failure

Date: 2026-01-30

## Problem

The `import_circular` test fails in `ir-eval` and `ir-eval-big-step` categories.

**Expected output**:
```
Import expansion error: Circular import detected: circular_a.ziku
Import chain: [...]
```

**Actual output**:
```
Translation error: Translation not implemented for import expression (should be expanded before translation) at 1:9
```

## Root Cause

The test runner functions (`runIREvalTest`, `runBigStepEvalFull`) do not call `expandImports` before translation, unlike `Main.lean`. The import expressions remain unexpanded, causing translation to fail with a different error.

## Fix

Modify `tests/TestRunner.lean` to add import expansion before translation in IR evaluation tests.

### Changes to `tests/TestRunner.lean`

**1. Update function signatures to accept file path:**

```lean
-- Line 187
def runIREvalTest (input : String) (inputPath : System.FilePath) : IO (Except String TestOutput) :=

-- Line 304
def runBigStepEvalFull (input : String) (inputPath : System.FilePath) : IO (Except String TestOutput) := do

-- Line 334
def runBigStepEvalTest (input : String) (inputPath : System.FilePath) : IO (Except String TestOutput) := do
```

**2. Add import expansion after parsing in `runIREvalTest` (around line 191):**

```lean
| .ok expr =>
  match ← Ziku.Import.expandImports inputPath expr with
  | .error msg => return .ok { output := s!"Import expansion error: {msg}", isError := true }
  | .ok expanded =>
    match Ziku.elaborateAll expanded with
    -- ... rest unchanged
```

**3. Add import expansion after parsing in `runBigStepEvalFull` (around line 308):**

```lean
| .ok expr =>
  match ← Ziku.Import.expandImports inputPath expr with
  | .error msg => return .ok { output := s!"Import expansion error: {msg}", isError := true }
  | .ok expanded =>
    match Ziku.elaborateAll expanded with
    -- ... rest unchanged
```

**4. Update call sites (around lines 425, 429, 336, 392):**

```lean
| "ir-eval" => runIREvalTest input tc.inputPath
| "ir-eval-big-step" => runBigStepEvalTest input tc.inputPath
```

And for internal calls:
```lean
match ← runBigStepEvalFull input inputPath with  -- line 336
let bigStepResult ← runBigStepEvalFull input tc.inputPath  -- line 392
```

## Verification

1. Build: `lake build`
2. Run failing test specifically:
   ```bash
   lake test -- ir-eval | grep -A2 import_circular
   ```
3. Run full test suite: `lake test`
4. Expected: 965 passed, 0 failed (the 2 failing tests should now pass)

## Files Modified

- `tests/TestRunner.lean`
