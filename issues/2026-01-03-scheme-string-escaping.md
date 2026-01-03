---
date: 2026-01-03
title: Scheme backend string escaping bug - quote characters not escaped
status: closed
---

# Scheme backend string escaping bug - quote characters not escaped

## Description

The Scheme backend does not properly escape quote characters (`"`) inside string literals when generating Scheme code. This causes syntax errors when Chez Scheme tries to parse the generated code.

## Context

- File: `Ziku/Backend/Scheme.lean`
- Function: `translateLit` (around line 47-50)
- Error manifests as: `Exception in read: unexpected end-of-file reading list`

## Example

Ziku source with embedded quote:
```ziku
let s = "\"" ++ "hello" ++ "\"" in s
```

Generated Scheme (incorrect):
```scheme
(string-append """ (string-append "hello" """))
```

Expected Scheme (correct):
```scheme
(string-append "\"" (string-append "hello" "\""))
```

## Affected Tests

The following tests fail due to this bug:
- `mal_step1_print_atoms` (uses `"\"" ++ s ++ "\""` pattern)
- `mal_step1_print_list`
- `mal_step1_types`
- `mal_step2_parse_atom`
- `mal_step2_read`
- `mal_step2_tokenize`

All these tests pass in IR evaluation but fail in Scheme execution.

## Proposed Fix

Update `translateLit` in `Ziku/Backend/Scheme.lean` to escape special characters:

```lean
def translateLit : Lit → String
  | .string s =>
    let escaped := s.replace "\\" "\\\\"  -- escape backslashes first
                    |>.replace "\"" "\\\""  -- then escape quotes
                    |>.replace "\n" "\\n"   -- escape newlines
                    |>.replace "\t" "\\t"   -- escape tabs
    s!"\"{escaped}\""
  | ...
```

## Related

- Focusing transformation commit: `5082ed5`
- IR evaluator handles strings correctly
- Only affects Scheme code generation path
