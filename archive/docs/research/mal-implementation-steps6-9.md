# MAL Implementation Steps 6-9: Detailed Guide for Ziku

Date: 2026-01-25

## Overview

This document provides a detailed technical guide for completing MAL steps 6-9 in Ziku, based on analysis of GitHub Issue #17 and the official MAL implementation guide.

**Issue**: [Complete MAL Implementation (#17)](https://github.com/takoeight0821/ziku/issues/17)

**Current Status**:
- Steps 0-5 are complete (implemented in `examples/mal/`)
- Steps 6-9 are missing

## Prerequisites

Before implementing steps 6-9, the following Ziku features are required:

### Existing Features (Available)
- `readLine` - Read line from stdin
- `println` - Print with newline
- String manipulation: `strLen`, `strAt`, `strSub`, `strToInt`, `intToStr`
- Character/Rune operations: `runeToStr`, `runeToInt`, `intToRune`
- `label`/`goto` for control flow (usable for exception handling)

### Features Needed for Step 6
- **`slurp`**: File reading function (needs Ziku extension or Scheme FFI)
- File system access for `load-file` functionality

---

## Step 6: Files, Mutation, and Evil

### Goals
1. Add `read-string` function (already have underlying `read_str`)
2. Add `slurp` function (read file contents)
3. Add `eval` function to REPL environment
4. Define `load-file` in MAL itself
5. Implement atoms (mutable state)

### Implementation Details

#### 6.1 `read-string` Function

This exposes the existing `read_str` function to MAL:

```ziku
-- In core functions
let read-string = \s => read_str s in
```

Add to `applyNative`:
```ziku
else if strEq op "read-string" then
  match args { | Cons(MStr(s), MNil) => read_str s | _ => MErr("read-string err") }
```

#### 6.2 `slurp` Function

**Option A: Add Ziku Builtin**

Extend `Ziku/Builtins.lean`:
```lean
| "slurp" => some .slurp
```

Add to `Ziku/Backend/Scheme.lean`:
```lean
| .slurp => s!"(call-with-input-file {argCodes[0]!} (lambda (p) (get-string-all p)))"
```

**Option B: Scheme FFI**

Use Scheme's file operations directly:
```ziku
-- Assuming extern support
let slurp = extern "slurp" -- maps to (call-with-input-file ...)
```

#### 6.3 `eval` Function

Add `eval` to the REPL environment as a closure:
```ziku
let replEnv =
  -- ... existing bindings ...
  let eN = envSet eN-1 "eval" (MEval) in  -- Special marker for eval
  eN
```

In `apply`:
```ziku
| MEval =>
  match args {
  | Cons(ast, MNil) => eval eval replEnv ast ~k  -- Uses captured replEnv
  }
```

#### 6.4 `load-file` Function

Define using MAL itself (in REPL initialization):
```mal
(def! load-file (fn* (f) (eval (read-string (str "(do " (slurp f) "\nnil)")))))
```

In Ziku:
```ziku
let rep = \env s =>
  pr_str (label k { eval eval env (read_str s) ~k })
in
let initEnv = rep replEnv "(def! load-file (fn* (f) (eval (read-string (str \"(do \" (slurp f) \"\\nnil)\")))))" in
```

#### 6.5 Atoms (Mutable State)

Atoms provide the only mutation in MAL. Implementation options:

**Option A: State-Passing Style**
```ziku
-- Atom is a unique ID referencing a value in a global state map
data MAtom = MAtom(Int)

-- State contains all atom values
let atomState = ref(HashMap.empty) in

let atomCreate = \val =>
  let id = nextAtomId() in
  atomState := HashMap.insert atomState id val;
  MAtom(id)
in
```

**Option B: Encapsulated Mutable Cell (via Scheme)**
```ziku
-- Use Scheme's boxes
-- atom  -> (box val)
-- deref -> (unbox atom)
-- reset! -> (set-box! atom val)
```

For Ziku's pure evaluation model, use state-passing with the environment.

**Core Atom Functions**:
```ziku
-- atom: Creates new atom with initial value
else if strEq op "atom" then
  match args { | Cons(val, MNil) => MAtom(val) | _ => MErr("atom err") }

-- atom?: Check if value is an atom
else if strEq op "atom?" then
  match args { | Cons(MAtom(_), MNil) => MTrue | _ => MFalse }

-- deref: Get atom's value
else if strEq op "deref" then
  match args { | Cons(MAtom(val), MNil) => val | _ => MErr("deref err") }

-- reset!: Set atom's value
else if strEq op "reset!" then
  match args {
  | Cons(MAtom(ref), Cons(newVal, MNil)) =>
    -- Need mutation mechanism here
    MAtom(newVal)  -- Returns new atom with updated value
  | _ => MErr("reset! err")
  }

-- swap!: Apply function to atom's value
else if strEq op "swap!" then
  match args {
  | Cons(MAtom(val), Cons(func, rest)) =>
    let newVal = apply ev func (Cons(val, rest)) env ~k in
    MAtom(newVal)  -- Returns updated atom
  | _ => MErr("swap! err")
  }
```

### Testing Step 6

Key tests from `step6_file.mal`:
```mal
(read-string "(1 2 (3 4) nil)")  ;=> (1 2 (3 4) nil)
(eval (read-string "(+ 2 3)"))   ;=> 5
(slurp "../tests/test.txt")      ;=> "A line of text\n"

(def! a (atom 2))                ;=> (atom 2)
(deref a)                        ;=> 2
(reset! a 3)                     ;=> 3
(swap! a (fn* (a) (* 2 a)))      ;=> 6
```

---

## Step 7: Quoting

### Goals
1. Add `cons` and `concat` core functions
2. Implement `quote` special form
3. Implement `quasiquote` function and special form

### Implementation Details

#### 7.1 Core Functions

```ziku
-- cons: Prepend element to list
else if strEq op "cons" then
  match args {
  | Cons(elem, Cons(lst, MNil)) => Cons(elem, lst)
  | _ => MErr("cons err")
  }

-- concat: Concatenate multiple lists
else if strEq op "concat" then
  let rec concatLists = \lists =>
    match lists {
    | MNil => MNil
    | Cons(lst, rest) => appendList lst (concatLists rest)
    }
  in concatLists args
```

Helper for append:
```ziku
let rec appendList = \l1 l2 =>
  match l1 {
  | MNil => l2
  | Cons(h, t) => Cons(h, appendList t l2)
  }
in
```

#### 7.2 `quote` Special Form

Returns argument unevaluated:
```ziku
| MSym("quote") =>
  match args {
  | Cons(form, MNil) => goto(Pair(form, env), k)
  | _ => goto(Pair(MErr("quote requires 1 arg"), env), k)
  }
```

#### 7.3 `quasiquote` Implementation

The `quasiquote` function transforms code before evaluation:

```ziku
let rec quasiquote = \ast =>
  match ast {
  -- If starts with unquote, return the second element
  | Cons(MSym("unquote"), Cons(form, MNil)) => form

  -- If it's a list
  | Cons(_, _) => quasiquoteList ast

  -- Symbols and maps need to be quoted
  | MSym(_) => Cons(MSym("quote"), Cons(ast, MNil))

  -- Other atoms return unchanged
  | _ => ast
  }
in

let rec quasiquoteList = \ast =>
  match ast {
  | MNil => MNil
  | Cons(Cons(MSym("splice-unquote"), Cons(form, MNil)), rest) =>
    -- (concat form (quasiquoteList rest))
    Cons(MSym("concat"), Cons(form, Cons(quasiquoteList rest, MNil)))
  | Cons(elt, rest) =>
    -- (cons (quasiquote elt) (quasiquoteList rest))
    Cons(MSym("cons"),
         Cons(quasiquote elt,
              Cons(quasiquoteList rest, MNil)))
  }
in
```

In evaluator:
```ziku
| MSym("quasiquote") =>
  match args {
  | Cons(form, MNil) =>
    let expanded = quasiquote form in
    ev ev env expanded ~k  -- TCO: evaluate the expanded form
  | _ => goto(Pair(MErr("quasiquote requires 1 arg"), env), k)
  }
```

### Testing Step 7

```mal
(cons 1 (list 2 3))              ;=> (1 2 3)
(concat (list 1 2) (list 3 4))   ;=> (1 2 3 4)
(quote (1 2 3))                  ;=> (1 2 3)
(quasiquote (1 2 3))             ;=> (1 2 3)
(def! lst (quote (b c)))
(quasiquote (a (unquote lst) d)) ;=> (a (b c) d)
(quasiquote (a (splice-unquote lst) d)) ;=> (a b c d)
```

---

## Step 8: Macros

### Goals
1. Add `is_macro` attribute to functions
2. Implement `defmacro!` special form
3. Handle macro expansion in EVAL

### Implementation Details

#### 8.1 Macro Type

Extend the closure type to include a macro flag:
```ziku
data MalType =
  | ...
  | MClosure(params, body, env)
  | MMacro(params, body, env)  -- New: Macro type
```

Or add flag to closure:
```ziku
| MClosure(params, body, env, isMacro)  -- Boolean flag
```

#### 8.2 `defmacro!` Special Form

```ziku
| MSym("defmacro!") =>
  match args {
  | Cons(MSym(name), Cons(value, MNil)) =>
    let res = label vk { ev ev env value ~vk } in
    match res {
    | Pair(MClosure(params, body, closedEnv), env2) =>
      let macro = MMacro(params, body, closedEnv) in
      let newEnv = envSet env2 name macro in
      goto(Pair(macro, newEnv), k)
    | _ => goto(Pair(MErr("defmacro! requires fn*"), env), k)
    }
  | _ => goto(Pair(MErr("defmacro! requires symbol and value"), env), k)
  }
```

#### 8.3 Macro Expansion in EVAL

Before normal function application, check if the function is a macro:

```ziku
-- In the application case
| _ =>
  -- First, evaluate only the function position
  let res = label ok { ev ev env head ~ok } in
  match res {
  | Pair(func, env2) =>
    match func {
    -- If macro: apply to UNEVALUATED args, then eval result
    | MMacro(params, body, closedEnv) =>
      let newEnvFrame = Cons(MNil, closedEnv) in
      let appliedEnv = bindParams params args newEnvFrame in  -- Note: args not evaluated
      let expanded = label mk { ev ev appliedEnv body ~mk } in
      match expanded {
      | Pair(newAst, _) => ev ev env2 newAst ~k  -- TCO: eval expanded form
      }

    -- If not macro: evaluate args normally
    | _ =>
      match evalList ev args env2 {
      | Pair(evaledArgs, env3) =>
        apply ev func evaledArgs env3 ~k
      }
    }
  }
```

### Testing Step 8

```mal
(defmacro! one (fn* () 1))
(one)                            ;=> 1

(defmacro! unless (fn* (pred a b) `(if ~pred ~b ~a)))
(unless false 7 8)               ;=> 7
(unless true 7 8)                ;=> 8
```

---

## Step 9: Try/Catch Exception Handling

### Goals
1. Implement `try*/catch*` special form
2. Implement `throw` core function
3. Add `apply` and `map` core functions
4. Add type predicates (`nil?`, `true?`, `false?`, `symbol?`)

### Implementation Details

#### 9.1 Exception Handling with `label`/`goto`

Ziku's `label`/`goto` can implement exception handling:

```ziku
| MSym("try*") =>
  match args {
  | Cons(tryBody, Cons(Cons(MSym("catch*"), Cons(MSym(excVar), Cons(catchBody, MNil))), MNil)) =>
    -- Create exception handler continuation
    label exceptionK {
      -- Try block: evaluate tryBody
      -- If throw is called, it will goto exceptionK
      let result = label normalK { ev ev env tryBody ~normalK } in
      match result {
      | Pair(MException(exc), _) =>
        -- Exception occurred: bind exception and evaluate catch body
        let catchEnv = envSet env excVar exc in
        ev ev catchEnv catchBody ~k
      | Pair(val, env2) =>
        -- Normal completion
        goto(Pair(val, env2), k)
      }
    }
  | Cons(tryBody, MNil) =>
    -- No catch clause: just evaluate try body
    ev ev env tryBody ~k
  | _ => goto(Pair(MErr("invalid try* form"), env), k)
  }
```

#### 9.2 `throw` Function

```ziku
-- Exception type
data MalType =
  | ...
  | MException(value)  -- Wraps any MAL value

-- throw function
else if strEq op "throw" then
  match args {
  | Cons(val, MNil) => MException(val)
  | _ => MErr("throw requires 1 arg")
  }
```

The exception propagates through the evaluator. Each eval call must check for exceptions:

```ziku
let checkException = \result k =>
  match result {
  | Pair(MException(exc), env) =>
    goto(Pair(MException(exc), env), k)  -- Propagate
  | _ => result  -- Continue normally
  }
```

#### 9.3 `apply` Function

```ziku
else if strEq op "apply" then
  match args {
  | Cons(func, rest) =>
    -- Last element is the list of remaining args
    let allArgs = flattenApplyArgs rest in
    apply ev func allArgs env ~k
  | _ => MErr("apply requires fn and args")
  }

let rec flattenApplyArgs = \args =>
  match args {
  | Cons(last, MNil) => last  -- Last arg is a list
  | Cons(arg, rest) => Cons(arg, flattenApplyArgs rest)
  | _ => MNil
  }
```

#### 9.4 `map` Function

```ziku
else if strEq op "map" then
  match args {
  | Cons(func, Cons(lst, MNil)) =>
    let rec mapList = \l =>
      match l {
      | MNil => MNil
      | Cons(elem, rest) =>
        let result = apply ev func (Cons(elem, MNil)) env ~k in
        match result {
        | Pair(val, _) => Cons(val, mapList rest)
        | _ => MErr("map error")
        }
      }
    in mapList lst
  | _ => MErr("map requires fn and list")
  }
```

#### 9.5 Type Predicates

```ziku
else if strEq op "nil?" then
  match args { | Cons(MNil, MNil) => MTrue | _ => MFalse }

else if strEq op "true?" then
  match args { | Cons(MTrue, MNil) => MTrue | _ => MFalse }

else if strEq op "false?" then
  match args { | Cons(MFalse, MNil) => MTrue | _ => MFalse }

else if strEq op "symbol?" then
  match args { | Cons(MSym(_), MNil) => MTrue | _ => MFalse }
```

### Testing Step 9

```mal
(throw "err1")                   ;=> Error: err1

(try* 123 (catch* e 456))        ;=> 123
(try* (throw "exc") (catch* e e)) ;=> "exc"

(apply + (list 2 3))             ;=> 5
(map (fn* (x) (* 2 x)) (list 1 2 3)) ;=> (2 4 6)

(nil? nil)                       ;=> true
(symbol? 'abc)                   ;=> true
```

---

## Implementation Strategy

### Recommended Order

1. **Step 6 First**: Add file I/O capabilities (requires Ziku extension for `slurp`)
2. **Step 7 Next**: Quoting is foundational for macros
3. **Step 8 Then**: Macros depend on quoting
4. **Step 9 Last**: Exception handling

### File Organization

Create new MAL step files in `examples/mal/`:
- `step6_file.ziku`
- `step7_quote.ziku`
- `step8_macros.ziku`
- `step9_try.ziku`

Each step should extend the previous step's functionality.

### Testing Against Official Tests

```bash
# Clone MAL for test files (already in vendor/)
cd /Users/y002168/ghq/github.com/takoeight0821/ziku

# Run specific test
docker run --rm ziku lake exe ziku < examples/mal/step6_file.ziku

# Compare with MAL tests
diff <(your_output) vendor/mal/tests/step6_file.mal
```

---

## Ziku Extensions Required

### Priority 1: File I/O (`slurp`)

Add builtin:
```lean
-- Ziku/Syntax.lean
inductive Builtin
  | ...
  | slurp  -- Read entire file as string

-- Ziku/Builtins.lean
| "slurp" => some .slurp

-- builtinArity
| .slurp => 1

-- builtinTypes
| "slurp" => some ([.con default "String"], .con default "String")

-- Ziku/Backend/Scheme.lean translateBuiltinApp
| .slurp =>
  let filename := argCodes[0]!
  s!"(call-with-input-file {filename} (lambda (p) (get-string-all p)))"
```

### Priority 2: Consider Mutation Model

For atoms, either:
- Extend Scheme backend to use boxes
- Use state-passing monad in Ziku evaluation

---

## Sources

- [MAL Process Guide](https://github.com/kanaka/mal/blob/master/process/guide.md)
- [MAL GitHub Repository](https://github.com/kanaka/mal)
- [Ziku MAL Issue #17](https://github.com/takoeight0821/ziku/issues/17)
- [LambdaConf 2016 Presentation](https://kanaka.github.io/lambdaconf/)
- [Existing Ziku MAL Research](./mal.md)
- [Ziku MAL Implementation Tracker](../../issues/2026-01-02-mal-implementation.md)
