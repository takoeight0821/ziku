# Fix High-Priority Issues from PR #66 Code Review

Date: 2026-02-06

## Context

PR #66 adds a module system to Ziku. Code review identified 4 high-priority issues:
1. Duplicate `ImportTypeMap` definition in two files
2. `expandImports` is 130 lines of verbose manual AST traversal
3. Duplicate path resolution in `expandImports` and `resolveImportTypes`
4. `expandImports` call copy-pasted 4 times in `Main.lean`

All fixes are structural refactors with no behavioral changes. All 962+ golden tests should pass without modification.

## Step 1: Move `ImportTypeMap` to `Ziku/Syntax.lean`

**Problem**: Defined identically in both `Ziku/Infer.lean:89` and `Ziku/Import.lean:17`.

**Changes**:
- `Ziku/Syntax.lean`: Add before `end Ziku` (line 582):
  ```lean
  /-- Mapping from import paths to their resolved types from signature files. -/
  abbrev ImportTypeMap := List (String × Ty)
  ```
- `Ziku/Infer.lean`: Delete lines 87-89 (comment + abbrev definition)
- `Ziku/Import.lean`: Delete lines 16-17 (comment + abbrev definition), add `ImportTypeMap` to the `open Ziku` on line 14

## Step 2: Extract `resolveImportPath` helper in `Ziku/Import.lean`

**Problem**: Both `resolveImportTypes` (line 46-51) and `expandImports` (line 78-82) independently create a path context and resolve imports.

**Changes** in `Ziku/Import.lean`:
- Add a private helper:
  ```lean
  private def resolveImportPath (basePath : System.FilePath) (importPath : String)
      : IO (Except String System.FilePath) := do
    let ctx := Ziku.Path.contextFromFile basePath
    match ← Ziku.Path.resolve ctx importPath with
    | .notFound tried =>
      return .error s!"Import file not found: {importPath}\nTried: {tried}"
    | .found resolvedPath =>
      return .ok resolvedPath
  ```
- Use it in `resolveImportTypes` and `expandImports` to replace the duplicated path resolution code

## Step 3: Refactor `expandImports` and `resolveImportTypes` to use `ExceptT`

**Problem**: `expandImports` (lines 73-200) manually matches `IO (Except String Expr)` in every branch, creating ~65 lines of boilerplate error threading.

**Changes** in `Ziku/Import.lean`:
- Change `expandImports` signature from `IO (Except String Expr)` to `ExceptT String IO Expr`
- Change `resolveImportTypes` signature from `IO (Except String ImportTypeMap)` to `ExceptT String IO ImportTypeMap`
- Update `resolveImportPath` to also use `ExceptT String IO`
- Replace `return .error msg` with `throw msg` and `return .ok x` with `return x`
- Each branch shrinks significantly. Example:
  ```lean
  -- Before (6 lines):
  | .binOp p op e1 e2 => do
    let e1' ← expandImports basePath e1 visited
    let e2' ← expandImports basePath e2 visited
    match e1', e2' with
    | .ok e1'', .ok e2'' => return .ok (.binOp p op e1'' e2'')
    | .error msg, _ => return .error msg
    | _, .error msg => return .error msg
  -- After (3 lines):
  | .binOp p op e1 e2 => do
    return .binOp p op (← expandImports basePath e1 visited) (← expandImports basePath e2 visited)
  ```
- List cases use `mapM` instead of mutable loops:
  ```lean
  -- Before (7 lines with mut + for + match):
  | .match_ p scrutinee cases => do
    let scrutinee' ← expandImports basePath scrutinee visited
    match scrutinee' with ...
      let mut newCases := []
      for (pat, body) in cases do ...
  -- After (4 lines):
  | .match_ p scrutinee cases => do
    let scrutinee' ← expandImports basePath scrutinee visited
    let cases' ← cases.mapM fun (pat, body) => do
      return (pat, ← expandImports basePath body visited)
    return .match_ p scrutinee' cases'
  ```

**Callers** (add `.run` to convert `ExceptT String IO X` back to `IO (Except String X)`):
- `Main.lean` lines 50, 69, 83, 98, 119: add `.run` (consolidated in Step 4)
- `tests/TestRunner.lean` lines 178, 192, 276, 300: add `.run`

## Step 4: Deduplicate `expandImports` calls in `Main.lean`

**Problem**: Lines 67-134 have 4 near-identical blocks each calling `expandImports` + error handling + `translateToStatement` + error handling.

**Changes** in `Main.lean`: Restructure `runOnInput` so `.translate`, `.scheme`, `.eval`, `.evalBigStep` share a single expand+translate block:
```lean
| _ =>
  -- All remaining modes need import expansion + translation
  match ← (expandImports basePath expr).run with
  | .error msg =>
    IO.eprintln s!"Import expansion error: {msg}"
    IO.Process.exit 1
  | .ok expanded =>
    match Translate.translateToStatement expanded with
    | .error err =>
      IO.eprintln s!"Translate error: {err}"
      IO.Process.exit 1
    | .ok stmt =>
      match mode with
      | .translate => IO.println s!"{stmt}"
      | .scheme => IO.println (Backend.Scheme.compile stmt)
      | .eval | .repl false =>
        match ← IR.eval stmt with
        | .value p _ => IO.println s!"{p}"
        | .stuck s _ => IO.eprintln s!"Stuck: {s}"; IO.Process.exit 1
        | .error msg => IO.eprintln s!"Eval error: {msg}"; IO.Process.exit 1
      | .evalBigStep | .repl true =>
        match ← IR.BigStepEval.eval stmt with
        | .value v => IO.println s!"{v}"
        | .error msg => IO.eprintln s!"Eval error: {msg}"; IO.Process.exit 1
      | .parse | .infer => pure ()  -- unreachable
```

This eliminates ~40 lines of duplicate error handling.

## Files Modified

| File | Steps | Changes |
|------|-------|---------|
| `Ziku/Syntax.lean` | 1 | Add `ImportTypeMap` abbrev |
| `Ziku/Infer.lean` | 1 | Remove duplicate `ImportTypeMap` |
| `Ziku/Import.lean` | 1, 2, 3 | Remove duplicate `ImportTypeMap`, extract helper, refactor to `ExceptT` |
| `Main.lean` | 3, 4 | Add `.run` calls, deduplicate expand+translate |
| `tests/TestRunner.lean` | 3 | Add `.run` to `expandImports`/`resolveImportTypes` call sites |

## Verification

```bash
# After each step, verify:
docker run --rm ziku lake build    # Build succeeds
docker run --rm ziku               # All golden tests pass (962+)
```
