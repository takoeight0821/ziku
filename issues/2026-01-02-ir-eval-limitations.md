---
date: 2026-01-02
title: IR evaluator limitations for string/rune operations
status: open
---

# IR evaluator limitations for string/rune operations

## Description

During MAL Phase 2 implementation, several limitations were discovered in the IR evaluator that prevent certain operations from working correctly.

## Issues Found

### 1. String equality comparison not supported

The `==` operator does not work for String comparison in the IR evaluator.

```ziku
// This fails with "Stuck" error
if tok == "nil" then MNil else MSym(tok)
```

**Workaround:** Implement custom `strEq` function using character-by-character comparison:

```ziku
let rec strEqFrom = \s1 s2 i =>
  if i >= strLen s1 then true
  else
    let c1 = runeToInt (strAt s1 i) in
    let c2 = runeToInt (strAt s2 i) in
    if c1 == c2 then strEqFrom s1 s2 (i + 1)
    else false
in

let strEq = \s1 s2 =>
  if strLen s1 == strLen s2 then strEqFrom s1 s2 0
  else false
in
```

### 2. Rune equality comparison not supported

The `==` operator does not work for Rune comparison in the IR evaluator.

```ziku
// This fails with "Stuck" error
if c == '(' then true else false
```

**Workaround:** Convert runes to integers before comparison:

```ziku
let code = runeToInt c in
if code == runeToInt '(' then true else false
```

### 3. Lazy evaluation issue with complex recursion

When combining tokenizer output with parser in a full `read` function, the IR evaluator gets stuck. The second element of Cons cells appears as suspended computation `(μ_α166. ⟨(fix tokenize...` instead of being evaluated.

```ziku
// This fails - tokenize result not fully evaluated when matched
let read = \s =>
  let tokens = tokenize s in
  match readForm tokens { ... }
```

**Status:** No workaround found. May require IR evaluator changes.

### 4. `&&` operator issue in Scheme backend

The `&&` operator generates incorrect Scheme code with wrong argument count.

```
Warning in compile: possible incorrect argument count in call ((lambda (a b) (if a b #f)))
```

**Status:** Scheme backend issue, not IR evaluator.

## Impact

- MAL Phase 2 individual components (tokenizer, parser) work correctly
- Full integration of `read` function (tokenize + parse) fails
- Workarounds exist for string/rune comparison issues

## Test Files Affected

- `tests/golden/ir-eval/success/mal_step2_helpers.ziku` - uses `&&`, fails in Scheme
- `tests/golden/ir-eval/success/mal_step2_parse_atom.ziku` - uses `strEq` workaround
- `tests/golden/ir-eval/success/mal_step2_read.ziku` - fails due to lazy evaluation

## Suggested Fixes

1. **String/Rune equality:** Add support for `==` on String and Rune types in IR evaluator
2. **Lazy evaluation:** Investigate why Cons cell elements remain suspended in complex recursion
3. **Scheme `&&`:** Fix argument count in generated Scheme code for logical operators

## Related

- MAL implementation plan: `docs/research/mal.md`
- Phase 2 plan: `.claude/plans/mutable-sparking-babbage.md`
