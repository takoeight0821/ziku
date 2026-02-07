# Plan: Add dedicated error constructor for codata in Translate

**Date**: 2026-02-08

## Context

`Translate.translateToStatement` currently throws `.notImplemented pos "codata block"` when it encounters a `.codata` node. Since the pipeline now runs `elaborateAll` before translation, codata blocks should never reach the translator. This is an invariant violation, not a missing feature, so it deserves its own error constructor with a clear message.

## Changes

### File: `Ziku/Translate.lean`

1. **Add new error constructor** to `TranslateError` (line 47-52):
   ```lean
   | unexpectedCodata (pos : SourcePos)
   ```

2. **Add `toString` case** in `TranslateError.toString` (line 55-57):
   ```lean
   | .unexpectedCodata pos => s!"Unexpected codata block at {pos.line}:{pos.col}: codata should be elaborated before translation"
   ```

3. **Use the new constructor** at line 309:
   ```lean
   | .codata pos _ => do
     throw $ .unexpectedCodata pos
   ```

## Verification

- `mise run docker:build-check`
- `mise run docker:test`
