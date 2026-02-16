---
date: 2026-01-02
title: MAL (Make A Lisp) Implementation in Ziku
status: in-progress
---

# MAL (Make A Lisp) Implementation in Ziku

## Progress

### Completed

- [x] **Phase 0**: String built-ins (`strLen`, `strAt`, `strSub`, `strToInt`, `intToStr`, `intToRune`, `runeToInt`, `runeToStr`)
- [x] **Phase 1**: Types and Print (Step 0)
  - `mal_step1_types.ziku`
  - `mal_step1_constructors.ziku`
  - `mal_step1_print_atoms.ziku`
  - `mal_step1_print_list.ziku`
- [x] **Phase 2**: Reader (Step 1)
  - `mal_step2_skip_ws.ziku`
  - `mal_step2_read_token.ziku`
  - `mal_step2_tokenize.ziku`
  - `mal_step2_helpers.ziku`
  - `mal_step2_parse_atom.ziku`
  - `mal_step2_read.ziku`
- [x] **Phase 3**: Eval & Environments (Step 2 & 3)
  - `mal_step3_eval.ziku` - Basic arithmetic evaluation
  - `mal_step3_def.ziku` - `def!`, `let*`, and persistent environment
- [x] **Phase 4**: Functions and Control Flow (Step 4)
  - `mal_step4_natives.ziku` - Native functions and printing
  - `mal_step4_control.ziku` - `if`, `do` control flow
  - `mal_step4_closure_def.ziku` - Closure definition with `fn*`
  - `mal_step4_fn_simple.ziku` - Simple function application
  - `mal_step4_fn_apply.ziku` - Full function application
- [x] **Phase 5**: Tail-Call Optimization (Step 5)
  - `mal_step5_tco_basic.ziku` - Basic TCO infrastructure
  - `mal_step5_tco_simple.ziku` - Simple CPS evaluation
  - `mal_step5_tco_if.ziku` - TCO for `if` expressions
  - `mal_step5_tco_do.ziku` - TCO for `do` blocks
  - `mal_step5_tco_fn.ziku` - TCO for function application
  - `mal_step5_tco_debug.ziku` - Debug tests for TCO
  - `mal_step5_tco_integration.ziku` (scheme-only) - Recursive factorial/count-evens

### In Progress

- [ ] **Phase 6**: File I/O and Atoms (Step 6)

### Blockers Resolved

- String/Rune equality comparison (fixed in `38aa3cf`)
- Lazy evaluation issue with recursive data (fixed in `5082ed5` via focusing transformation)
- Scheme string escaping (fixed in `b6e1217`)
- Wildcard pattern matching (fixed in `aa54f4f`)

---

## Goal

Implement a **self-hosting capable MAL** with a **string-based reader** as **incremental test files**.

## Prerequisites: Ziku Extensions Required

### Phase 0: Add String Built-ins to Ziku

**Files modified:** `Ziku/Syntax.lean`, `Ziku/IR/Syntax.lean`, `Ziku/IR/Eval.lean`, `Ziku/Translate.lean`, `Ziku/Parser.lean`

---

## MAL Implementation Phases

### Phase 1: Types and PRINT (Step 0)

**File:** `tests/golden/ir-eval/success/mal_step1_types.ziku`

### Phase 2: READ (Step 1)

**Files:**

- `tests/golden/ir-eval/success/mal_step1_tokenize.ziku` (Tokenizer)
- `tests/golden/ir-eval/success/mal_step1_read.ziku` (Parser)

### Phase 3: EVAL & Environments (Step 2 & 3)

**Files:**

- `tests/golden/ir-eval/success/mal_step3_eval.ziku` (Basic Arithmetic)
- `tests/golden/ir-eval/success/mal_step3_def.ziku` (Environments, `def!`, `let*`)

### Phase 4: Functions and Control Flow (Step 4)

**File:** `tests/golden/ir-eval/success/mal_step4_fn.ziku`

- `if` conditional
- `do` sequential evaluation
- `fn*` closures

```ziku
| MList(Cons(MSym("fn*"), Cons(MList(params), Cons(body, Nil)))) =>
  MClosure(params, body, env)
```

### Phase 5: Tail-Call Optimization (Step 5)

**Files:**

- `tests/golden/ir-eval/success/mal_step5_tco_basic.ziku`
- `tests/golden/ir-eval/success/mal_step5_tco_simple.ziku`
- `tests/golden/ir-eval/success/mal_step5_tco_if.ziku`
- `tests/golden/ir-eval/success/mal_step5_tco_do.ziku`
- `tests/golden/ir-eval/success/mal_step5_tco_fn.ziku`
- `tests/golden/ir-eval/success/mal_step5_tco_debug.ziku`
- `tests/golden/scheme-only/mal_step5_tco_integration.ziku`

Transform recursive EVAL calls to loop using `label`/`goto`. Note that `mal_step5_tco_integration.ziku` is a scheme-only test due to IR evaluator limits.

### Phase 6: File I/O and Atoms (Step 6)

**File:** `tests/golden/ir-eval/success/mal_step6_atoms.ziku`

Atoms (mutable state) via state-passing and `read-string`/`slurp`.

### Phase 7: Quoting (Step 7)

**File:** `tests/golden/ir-eval/success/mal_step7_quote.ziku`

- `quote`
- `quasiquote`

### Phase 8: Macros (Step 8)

**File:** `tests/golden/ir-eval/success/mal_step8_macros.ziku`

- `defmacro!`
- `macroexpand`

### Phase 9: Exception Handling (Step 9)

**File:** `tests/golden/ir-eval/success/mal_step9_try.ziku`

Using Ziku's `label`/`goto` for `try*`/`catch*`.

### Phase 10: Self-Hosting (Step A)

**File:** `tests/golden/ir-eval/success/mal_stepA_mal.ziku`

Complete implementation with metadata support and self-hosting test.

---

## Test Files Summary

### Implemented Tests

| File                             | Status | Features                     |
| -------------------------------- | ------ | ---------------------------- |
| `mal_step1_types.ziku`           | ✅     | MAL types                    |
| `mal_step1_constructors.ziku`    | ✅     | Constructors                 |
| `mal_step1_print_*.ziku`         | ✅     | Printer                      |
| `mal_step2_*.ziku`               | ✅     | Reader (Tokenizer + Parser)  |
| `mal_step3_eval.ziku`            | ✅     | Basic Eval (Step 2)          |
| `mal_step3_def.ziku`             | ✅     | Env, def!, let\* (Step 3)    |
| `mal_step4_natives.ziku`         | ✅     | Native functions (Step 4)    |
| `mal_step4_control.ziku`         | ✅     | if, do control flow (Step 4) |
| `mal_step4_closure_def.ziku`     | ✅     | fn\* closures (Step 4)       |
| `mal_step4_fn_simple.ziku`       | ✅     | Simple application (Step 4)  |
| `mal_step4_fn_apply.ziku`        | ✅     | Full application (Step 4)    |
| `mal_step5_tco_basic.ziku`       | ✅     | Basic TCO infra (Step 5)     |
| `mal_step5_tco_simple.ziku`      | ✅     | Simple CPS (Step 5)          |
| `mal_step5_tco_if.ziku`          | ✅     | TCO if (Step 5)              |
| `mal_step5_tco_do.ziku`          | ✅     | TCO do (Step 5)              |
| `mal_step5_tco_fn.ziku`          | ✅     | TCO application (Step 5)     |
| `mal_step5_tco_debug.ziku`       | ✅     | TCO debug (Step 5)           |
| `mal_step5_tco_integration.ziku` | ✅     | TCO integration (Step 5)     |

### Planned Tests

| File                    | Features              |
| ----------------------- | --------------------- |
| `mal_step6_atoms.ziku`  | Atoms, I/O (Step 6)   |
| `mal_step7_quote.ziku`  | Quoting (Step 7)      |
| `mal_step8_macros.ziku` | Macros (Step 8)       |
| `mal_step9_try.ziku`    | Exceptions (Step 9)   |
| `mal_stepA_mal.ziku`    | Self-hosting (Step A) |

---

## Implementation Order

1. **Phase 0**: Add string primitives to Ziku (✅)
2. **Phase 1**: Types & Print (Step 0) (✅)
3. **Phase 2**: Reader (Step 1) (✅)
4. **Phase 3**: Eval & Environments (Step 2 & 3) (✅)
5. **Phase 4**: Functions (Step 4) (✅)
6. **Phase 5**: TCO (Step 5) (✅)
7. **Phase 6**: Atoms (Step 6)
8. **Phase 7**: Quoting (Step 7)
9. **Phase 8**: Macros (Step 8)
10. **Phase 9**: Exceptions (Step 9)
11. **Phase 10**: Self-hosting test (Step A)
