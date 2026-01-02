---
date: 2026-01-02
title: MAL (Make A Lisp) Implementation in Ziku
status: in-progress
---

# MAL (Make A Lisp) Implementation in Ziku

## Progress

### Completed

- [x] **Phase 0**: String built-ins (`strLen`, `strAt`, `strSub`, `strToInt`, `intToStr`, `intToRune`, `runeToInt`, `runeToStr`)
- [x] **Phase 1**: MAL types and prStr function
  - `mal_step1_types.ziku` - Type constructors (MNum, MSym, MStr, MNil, MBool, MList, MCons)
  - `mal_step1_constructors.ziku` - Basic data constructors
  - `mal_step1_print_atoms.ziku` - prStr for atoms
  - `mal_step1_print_list.ziku` - prStr for lists
- [x] **Phase 2**: READ (tokenizer + parser)
  - `mal_step2_skip_ws.ziku` - Whitespace skipping
  - `mal_step2_read_token.ziku` - Single token reading
  - `mal_step2_tokenize.ziku` - Full tokenizer
  - `mal_step2_helpers.ziku` - Helper functions
  - `mal_step2_parse_atom.ziku` - Atom parsing
  - `mal_step2_read.ziku` - Full read function (tokenize + parse integrated)

### In Progress

- [ ] **Phase 3**: Basic EVAL with environments

### Blockers Resolved

- String/Rune equality comparison (fixed in `38aa3cf`)
- Lazy evaluation issue with recursive data (fixed in `5082ed5` via focusing transformation)
- Scheme string escaping (fixed in `b6e1217`)
- Wildcard pattern matching (fixed in `aa54f4f`)

---

## Goal

Implement a **self-hosting capable MAL** with a **string-based reader** as **incremental test files**.

## Prerequisites: Ziku Extensions Required

Before implementing MAL, Ziku needs string manipulation primitives:

### Phase 0: Add String Built-ins to Ziku

**Files to modify:**

- `Ziku/Syntax.lean` - Add new built-in operations
- `Ziku/IR/Syntax.lean` - Add IR representation
- `Ziku/IR/Eval.lean` - Implement evaluation
- `Ziku/Translate.lean` - Surface to IR translation
- `Ziku/Parser.lean` - Parse new syntax

**New operations needed:**

```
strLen(s)        -- String length
strAt(s, i)      -- Character at index (returns Int/Char)
strSub(s, i, n)  -- Substring from index i, length n
strToInt(s)      -- Parse string to integer
intToStr(n)      -- Integer to string
```

---

## MAL Implementation Phases

### Phase 1: Types and PRINT (Steps 0-1)

**File:** `tests/golden/ir-eval/success/mal_step1_types.ziku`

```ziku
-- MAL value constructors
-- MNum(n), MSym(s), MStr(s), MNil, MBool(b), MList(cells)
-- MClosure(params, body, env), MBuiltin(name), MMacro(params, body, env)

let rec prStr = \val =>
  match val {
  | MNum(n) => intToStr n
  | MSym(s) => s
  | MStr(s) => "\"" ++ s ++ "\""
  | MNil => "nil"
  | MBool(b) => if b then "true" else "false"
  | MList(lst) => "(" ++ prList lst ++ ")"
  | MClosure(_, _, _) => "#<function>"
  | MBuiltin(_) => "#<builtin>"
  | MMacro(_, _, _) => "#<macro>"
  }
in ...
```

### Phase 2: READ - Tokenizer (Step 1a)

**File:** `tests/golden/ir-eval/success/mal_step1_tokenize.ziku`

Tokenize MAL source string into list of token strings:

- Whitespace/comma handling
- Special characters: `(`, `)`, `[`, `]`, `{`, `}`, `'`, `` ` ``, `~`, `~@`, `@`, `^`
- Strings with escape sequences
- Comments (`;` to end of line)
- Symbols and numbers

### Phase 3: READ - Parser (Step 1b)

**File:** `tests/golden/ir-eval/success/mal_step1_read.ziku`

```ziku
let rec readForm = \tokens =>
  match tokens {
  | Cons(token, rest) =>
    if token == "(" then readList rest
    else if token == "[" then readVector rest
    else if token == "'" then readQuote "quote" rest
    else readAtom token rest
  | Nil => Pair(MNil, Nil)
  }
```

### Phase 4: Basic EVAL (Step 2)

**File:** `tests/golden/ir-eval/success/mal_step2_eval.ziku`

Basic evaluation without environments:

- Self-evaluating: numbers, strings, booleans, nil
- Apply arithmetic: `+`, `-`, `*`, `/`

### Phase 5: Environments (Step 3)

**File:** `tests/golden/ir-eval/success/mal_step3_env.ziku`

```ziku
-- Environment as association list with outer pointer
let emptyEnv = MEnv(Nil, MNil)

let envSet = \env => \sym => \val =>
  match env { | MEnv(data, outer) => MEnv(Cons(Pair(sym, val), data), outer) }

let rec envGet = \env => \sym =>
  match env {
  | MEnv(data, outer) =>
    match lookup sym data {
    | Just(v) => v
    | Nothing => match outer { | MEnv(_, _) => envGet outer sym | MNil => MErr("not found") }
    }
  }
```

Special forms: `def!`, `let*`

### Phase 6: Functions and Control Flow (Step 4)

**File:** `tests/golden/ir-eval/success/mal_step4_fn.ziku`

- `if` conditional
- `do` sequential evaluation
- `fn*` closures

```ziku
| MList(Cons(MSym("fn*"), Cons(MList(params), Cons(body, Nil)))) =>
  MClosure(params, body, env)
```

### Phase 7: Tail-Call Optimization (Step 5)

**File:** `tests/golden/ir-eval/success/mal_step5_tco.ziku`

Transform recursive EVAL calls to loop using `label`/`goto`:

```ziku
let rec eval = \ast => \env =>
  label tco_loop {
    match ast {
    -- ... special forms that recur via goto ...
    | MList(Cons(MSym("if"), Cons(cond, Cons(thenE, rest)))) =>
      let c = eval cond env in
      if isTruthy c
      then goto(Pair(thenE, env), tco_loop)  -- TCO: continue loop
      else match rest {
        | Cons(elseE, Nil) => goto(Pair(elseE, env), tco_loop)
        | Nil => MNil
      }
    }
  }
```

### Phase 8: File I/O and Atoms (Step 6)

**File:** `tests/golden/ir-eval/success/mal_step6_atoms.ziku`

Atoms (mutable state) via state-passing:

```ziku
-- Thread state through evaluation
-- eval : Ast -> Env -> World -> (Value, World)

let evalAtom = \args => \env => \world =>
  let Pair(val, w1) = eval (head args) env world in
  let id = freshAtomId w1 in
  let w2 = setAtom w1 id val in
  Pair(MAtom(id), w2)
```

Also: `eval` function, `read-string`, `slurp`

### Phase 9: Quoting (Step 7)

**File:** `tests/golden/ir-eval/success/mal_step7_quote.ziku`

- `quote` - return unevaluated
- `quasiquote` - template with `unquote` and `splice-unquote`

```ziku
let rec quasiquote = \ast =>
  match ast {
  | MList(Cons(MSym("unquote"), Cons(x, Nil))) => x
  | MList(Cons(MList(Cons(MSym("splice-unquote"), Cons(x, Nil))), rest)) =>
    MList(Cons(MSym("concat"), Cons(x, Cons(quasiquote (MList rest), Nil))))
  | MList(lst) => MList(Cons(MSym("cons"), Cons(quasiquote (head lst), Cons(quasiquote (MList (tail lst)), Nil))))
  | _ => MList(Cons(MSym("quote"), Cons(ast, Nil)))
  }
```

### Phase 10: Macros (Step 8)

**File:** `tests/golden/ir-eval/success/mal_step8_macros.ziku`

```ziku
-- defmacro! creates MMacro instead of MClosure
| MList(Cons(MSym("defmacro!"), Cons(MSym(name), Cons(fn, Nil)))) =>
  let closure = eval fn env in
  match closure { | MClosure(p, b, e) => envSet env name (MMacro(p, b, e)) }

-- macroexpand before EVAL
let rec macroexpand = \ast => \env =>
  match ast {
  | MList(Cons(MSym(s), args)) =>
    match envGet env s {
    | MMacro(params, body, macroEnv) =>
      let newEnv = bindParams params args macroEnv in  -- UNEVALUATED args
      let expanded = eval body newEnv in
      macroexpand expanded env
    | _ => ast
    }
  | _ => ast
  }
```

### Phase 11: Exception Handling (Step 9)

**File:** `tests/golden/ir-eval/success/mal_step9_try.ziku`

Using Ziku's `label`/`goto` for `try*`/`catch*`:

```ziku
| MList(Cons(MSym("try*"), Cons(body, Cons(MList(Cons(MSym("catch*"), Cons(MSym(e), Cons(handler, Nil)))), Nil)))) =>
  label catch {
    evalWithThrow body env catch  -- errors goto catch with error value
  }
  -- label captures error, binds to e, evals handler
```

### Phase 12: Self-Hosting (Step A)

**File:** `tests/golden/ir-eval/success/mal_stepA_mal.ziku`

Complete implementation with:

- All core functions
- Metadata support (`meta`, `with-meta`)
- `*host-language*` set to "Ziku"

Test self-hosting by running MAL's `stepA_mal.mal` on our implementation.

---

## Test Files Summary

### Implemented Tests

| File                          | Status | Features                           |
| ----------------------------- | ------ | ---------------------------------- |
| `mal_step1_types.ziku`        | ✅     | MAL types and constructors         |
| `mal_step1_constructors.ziku` | ✅     | Basic data constructors            |
| `mal_step1_print_atoms.ziku`  | ✅     | prStr for atoms (num, sym, nil)    |
| `mal_step1_print_list.ziku`   | ✅     | prStr for lists                    |
| `mal_step2_skip_ws.ziku`      | ✅     | Whitespace skipping                |
| `mal_step2_read_token.ziku`   | ✅     | Single token reading               |
| `mal_step2_tokenize.ziku`     | ✅     | Full tokenizer                     |
| `mal_step2_helpers.ziku`      | ✅     | Helper functions (lookup, etc.)    |
| `mal_step2_parse_atom.ziku`   | ✅     | Atom parsing (num, sym, nil, bool) |
| `mal_step2_read.ziku`         | ✅     | Full read function                 |

### Planned Tests

| File                    | Features                  |
| ----------------------- | ------------------------- |
| `mal_step3_eval.ziku`   | Basic eval                |
| `mal_step4_env.ziku`    | Environments, def!, let\* |
| `mal_step5_fn.ziku`     | if, do, fn\*, closures    |
| `mal_step6_tco.ziku`    | Tail-call optimization    |
| `mal_step7_atoms.ziku`  | Atoms, eval, read-string  |
| `mal_step8_quote.ziku`  | quote, quasiquote         |
| `mal_step9_macros.ziku` | defmacro!, macroexpand    |
| `mal_stepA_try.ziku`    | try*/catch*, throw        |
| `mal_stepB_mal.ziku`    | Full implementation       |

---

## Critical Files to Modify

### Ziku Extensions (Phase 0)

- `Ziku/Syntax.lean:26-36` - Add new BinOp or create UnaryOp for string ops
- `Ziku/IR/Syntax.lean` - Add IR representations
- `Ziku/IR/Eval.lean` - Implement string operation evaluation
- `Ziku/Translate.lean` - Surface to IR translation
- `Ziku/Parser.lean` - Parse string function calls
- `Ziku/Infer.lean` - Type inference for string operations

### Reference Files

- `tests/golden/ir-eval/success/lisp_10_eval_arith.ziku` - Existing eval pattern
- `tests/golden/ir-eval/success/label_loop.ziku` - label/goto for TCO
- `docs/research/mal.md` - MAL specification

---

## Implementation Order

1. **Phase 0**: Add string primitives to Ziku (required for everything else)
2. **Phase 1-3**: Types, tokenizer, parser (READ)
3. **Phase 4-5**: Basic EVAL with environments
4. **Phase 6**: Closures and control flow
5. **Phase 7**: TCO using label/goto
6. **Phase 8**: Atoms with state-passing
7. **Phase 9-10**: Quoting and macros
8. **Phase 11**: Exceptions using label/goto
9. **Phase 12**: Self-hosting test

---

## Open Questions Resolved

- **Scope**: Self-hosting capable (all 11 MAL steps)
- **Input**: String-based reader (requires Ziku string extensions)
- **Organization**: Incremental test files in `tests/golden/ir-eval/success/`
- **Mutable state**: State-passing style (thread `World` through eval)
- **TCO/Exceptions**: Use Ziku's `label`/`goto` primitives
