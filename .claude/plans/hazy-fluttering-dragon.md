# Plan: Use unhygienic-proof prefix for compiler-generated variables

**Date**: 2026-02-08
**Issue**: #74

## Context

The elaboration phase uses hardcoded variable names (`_copat_arg`, `_pat_arg`) that could collide with user-defined identifiers. Other passes (Translate, Focusing, IR/Eval) also generate names using `_` prefix which users can write. The `#` character is NOT valid in user identifiers (Lexer.lean only allows alphanumeric, `_`, `'`), making it an ideal prefix for compiler-generated names. The Scheme backend's `mangleIdent` already handles `#` → `_hash_`.

## Approach

### Step 1: Create `Ziku/FreshName.lean` utility module

Central module providing:
- `hygienicPrefix` constant (`"#"`)
- `fresh (base : String) (counter : Nat) : Ident` → `"#base{counter}"`
- Constants for pseudo-constructors: `wildCon` (`"#wild"`), `varCon` (`"#var"`), `litIntPrefix` (`"#lit_int_"`), etc.

Add `import Ziku.FreshName` to `Ziku.lean`.

### Step 2: Update Elaborate.lean — add counter-based generation

- Define `ElabM := StateT Nat (Except ElaborateError)` monad
- Change `elaborate`, `elaborateWithPatternGuards`, `elaboratePatternMatch` to use `ElabM`
- Change `elaborateAll` to use `ElabM`, run with initial counter 0 at public entry point
- Replace `"_pat_arg"` (line 197) → `FreshName.fresh "pat_arg" counter`
- Replace `"_copat_arg"` (line 315) → `FreshName.fresh "copat_arg" counter`

### Step 3: Update Translate.lean — use `#` prefix

- `freshCovar`: `"_α{n}"` → `FreshName.fresh "α" n` (line 78)
- `freshVar`: `"_tmp{n}"` → `FreshName.fresh "tmp" n` (line 134)
- Wildcard extraction: `"_wild{n}"` → `FreshName.fresh "wild" n` (line 199)
- `litToConName`: `"_lit_int_{n}"` etc. → use `FreshName.litIntPrefix` etc. (lines 124-129)
- `"_var"` → `FreshName.varCon`, `"_wild"` → `FreshName.wildCon` (lines 177, 180, 384, 412, 427)

### Step 4: Update IR/Focusing.lean — use `#` prefix

- `freshVar`: `"_f{n}"` → `FreshName.fresh "f" n` (line 39)

### Step 5: Update IR/Eval.lean — use `#` prefix and constants

- Static names: `"_binop_l"` → `FreshName.static "binop_l"`, etc. (lines 315-330)
- `"_dataCon_arg{idx}"` → `FreshName.fresh "dataCon_arg" idx` (line 353)
- `"_original_c"` → `FreshName.static "original_c"` (lines 355-356)
- Pseudo-constructor matching: `"_wild"` → `FreshName.wildCon`, `"_var"` → `FreshName.varCon`, literal prefixes (lines 378-425)

### Step 6: Update IR/BigStepEval.lean — use `#` prefix constants

- Same pseudo-constructor constant changes as Eval.lean (lines ~283-306)

### Step 7: Update Backend/Scheme.lean — use constants for prefix matching

- `"_wild"` / `"_var"` → `FreshName.wildCon` / `FreshName.varCon` (line 246)
- `"_lit_"` prefix checks → `FreshName.litPrefix` (line 247)
- Hardcoded `.drop 9`, `.drop 10`, `.drop 12` → `.drop FreshName.litIntPrefix.length` etc. (lines 252-260)

## Files to modify

| File | Change |
|------|--------|
| `Ziku/FreshName.lean` | **NEW** — central utility |
| `Ziku.lean` | Add import |
| `Ziku/Elaborate.lean` | ElabM monad + `#` prefix |
| `Ziku/Translate.lean` | `#` prefix for all generated names |
| `Ziku/IR/Focusing.lean` | `#` prefix |
| `Ziku/IR/Eval.lean` | `#` prefix + constants |
| `Ziku/IR/BigStepEval.lean` | Constants |
| `Ziku/Backend/Scheme.lean` | Constants + length-based drop |

## Golden tests

No golden files contain generated variable names (verified via grep). No updates needed.

## Verification

1. `mise run docker:build-check` — build succeeds
2. `mise run docker:test` — all tests pass
3. Manually verify `#` appears in IR output for a codata test: `mise run docker:run ir-eval tests/golden/ir-eval/success/codata_field.ziku`
