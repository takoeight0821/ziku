# mal (Make a Lisp): A Clojure-Inspired Lisp Learning Tool

## Overview

- **Repository**: [github.com/kanaka/mal](https://github.com/kanaka/mal)
- **Author**: Joel Martin (kanaka)
- **License**: MPL 2.0 (Mozilla Public License 2.0)
- **Created**: March 2014
- **Stars**: 10,500+
- **Forks**: 2,600+
- **Implementations**: 89 languages (95 implementations, 118 runtime modes)

mal is a Clojure-inspired Lisp interpreter designed as both a functional programming language and an educational framework. The goal is to make it easy to write your own Lisp interpreter without sacrificing the "Aha!" moments that come from understanding McCarthy's original insights. The final implementation is powerful enough to be **self-hosting**—it can run a mal interpreter written in mal itself.

## Language Features

### Syntax (Clojure-like)

```clojure
;; Primitives
42              ; integer
3.14            ; float
"hello"         ; string
:keyword        ; keyword (stored with special prefix)
true false nil  ; booleans and nil

;; Collections
(1 2 3)         ; list
[1 2 3]         ; vector
{:a 1 :b 2}     ; hash-map

;; Symbols and evaluation
(def! x 42)                     ; define variable
(let* [a 1 b 2] (+ a b))        ; local bindings
(fn* [x y] (+ x y))             ; anonymous function
(if cond then else)             ; conditional
(do expr1 expr2 ...)            ; sequential evaluation

;; Functions
(defn! square [x] (* x x))      ; named function (macro)
((fn* [x] (* x x)) 5)           ; immediately invoked

;; Quoting and macros
(quote (1 2 3))                 ; prevent evaluation
'(1 2 3)                        ; shorthand for quote
`(1 ~x ~@xs)                    ; quasiquote with unquote
(defmacro! name [args] body)    ; macro definition

;; Exception handling
(try* expr (catch* e handler))  ; try/catch
(throw "error")                 ; throw exception
```

### Special Forms

| Form | Description |
|------|-------------|
| `def!` | Bind value to symbol in current environment |
| `let*` | Create local bindings (sequential, can refer to earlier bindings) |
| `fn*` | Create anonymous function with closure |
| `if` | Conditional evaluation |
| `do` | Sequential evaluation, return last |
| `quote` | Return argument unevaluated |
| `quasiquote` | Template with selective evaluation |
| `defmacro!` | Define a macro |
| `try*/catch*` | Exception handling |

### Core Functions

**List operations**: `list`, `list?`, `empty?`, `count`, `first`, `rest`, `nth`, `cons`, `concat`, `seq`

**Predicates**: `nil?`, `true?`, `false?`, `symbol?`, `keyword?`, `vector?`, `map?`, `fn?`, `macro?`

**Arithmetic**: `+`, `-`, `*`, `/`, `<`, `<=`, `>`, `>=`, `=`

**I/O**: `prn`, `println`, `pr-str`, `str`, `read-string`, `slurp`, `readline`

**Higher-order**: `map`, `apply`, `throw`

**Atoms (mutable state)**: `atom`, `deref`/`@`, `reset!`, `swap!`

**Metadata**: `meta`, `with-meta`

## Architecture

### 11 Incremental Steps

The implementation is divided into 11 self-contained, testable steps:

```
step0_repl      → Basic REPL skeleton
step1_read_print → Reader (tokenizer + parser) and printer
step2_eval      → Expression evaluation (calculator)
step3_env       → Environments, def!, let*
step4_if_fn_do  → Conditionals, closures, do
step5_tco       → Tail-call optimization
step6_file      → File I/O, atoms, eval
step7_quote     → quote, quasiquote, macros foundation
step8_macros    → defmacro!, macro expansion
step9_try       → Exception handling
stepA_mal       → Metadata, self-hosting
```

### Core Components

```
┌─────────────────────────────────────────────────────┐
│                     REPL Loop                        │
│              READ → EVAL → PRINT                     │
└─────────────────────────────────────────────────────┘
                        │
        ┌───────────────┼───────────────┐
        ▼               ▼               ▼
┌───────────────┐ ┌───────────────┐ ┌───────────────┐
│    Reader     │ │   Evaluator   │ │    Printer    │
│  (tokenize +  │ │ (eval_ast +   │ │  (pr_str)     │
│    parse)     │ │  EVAL)        │ │               │
└───────────────┘ └───────────────┘ └───────────────┘
                        │
                        ▼
              ┌───────────────────┐
              │   Environment     │
              │  (symbol table    │
              │   with lexical    │
              │   scoping)        │
              └───────────────────┘
```

### Type System (C Implementation Example)

```c
enum mal_type_t {
    MALTYPE_SYMBOL   = 1 << 0,
    MALTYPE_KEYWORD  = 1 << 1,
    MALTYPE_INTEGER  = 1 << 2,
    MALTYPE_FLOAT    = 1 << 3,
    MALTYPE_STRING   = 1 << 4,
    MALTYPE_TRUE     = 1 << 5,
    MALTYPE_FALSE    = 1 << 6,
    MALTYPE_NIL      = 1 << 7,
    MALTYPE_LIST     = 1 << 8,
    MALTYPE_VECTOR   = 1 << 9,
    MALTYPE_HASHMAP  = 1 << 10,
    MALTYPE_FUNCTION = 1 << 11,
    MALTYPE_CLOSURE  = 1 << 12,
    MALTYPE_ATOM     = 1 << 13,
    MALTYPE_MACRO    = 1 << 14
};
```

For OOP languages, a `MalType` base class/interface with subclasses for each type is typical. For dynamically typed languages, native types can often be used directly.

### Environment Structure

```
┌─────────────────────────────────────────┐
│ Environment                             │
│  ├── data: HashMap<Symbol, MalType>     │
│  └── outer: Option<Environment>         │
├─────────────────────────────────────────┤
│ Methods:                                │
│  • set(symbol, value)                   │
│  • find(symbol) → Environment?          │
│  • get(symbol) → MalType                │
└─────────────────────────────────────────┘
```

Lookup traverses the chain: current → outer → outer.outer → ... → root

### Closure Structure

```
┌─────────────────────────────────────────┐
│ Closure                                 │
│  ├── env: Environment (captured)        │
│  ├── params: List<Symbol>               │
│  └── body: MalType (AST)                │
└─────────────────────────────────────────┘
```

When called, creates new environment with params bound to args, outer = captured env.

## Implementation Details

### Reader Algorithm

1. **Tokenize**: Regex-based tokenizer extracts tokens
   - Pattern: `[\s,]*(~@|[\[\]{}()'`~^@]|"(?:\\.|[^\\"])*"?|;.*|[^\s\[\]{}('"`,;)]*)`
2. **Read Form**: Dispatch on first character
   - `(` → read_list
   - `[` → read_vector
   - `{` → read_hashmap
   - `'`, `` ` ``, `~`, `~@`, `@` → reader macros
   - Otherwise → read_atom
3. **Read Atom**: Numbers, strings, keywords, symbols, nil, true, false

### Evaluation Rules

```
EVAL(ast, env):
  1. If ast is not a list → eval_ast(ast, env)
  2. If ast is empty list → return ast
  3. If ast[0] is special form → handle specially
  4. Otherwise (function call):
     a. Evaluate all elements
     b. If first is closure → TCO loop
     c. If first is native fn → call directly
```

### Tail-Call Optimization

Convert recursive EVAL calls to loop iterations for tail positions:

```python
def EVAL(ast, env):
    while True:
        # ... handle special forms ...
        if is_tail_position:
            ast = new_ast
            env = new_env
            continue  # Loop instead of recurse
        else:
            return recursive_EVAL(...)
```

### Macro Expansion

```
1. Check if ast[0] is symbol bound to macro
2. If yes: call macro with UNEVALUATED args
3. Macro returns new AST
4. EVAL the returned AST (may expand again)
```

## Testing Infrastructure

- **~800 tests** in `tests/` directory
- **Test harness**: `runtest.py` using pexpect
- **Docker support**: Pre-built images for all implementations

```bash
# Run tests for specific step
make "test^python^step3"

# Run all tests for implementation
make "test^rust"

# Self-hosted mode
make MAL_IMPL=python3 "test^mal^step2"

# Start REPL at specific step
make "repl^ruby^step4"
```

## Related Projects

### miniMAL

- **Repository**: [github.com/kanaka/miniMAL](https://github.com/kanaka/miniMAL)
- A "delightfully diminutive" Lisp in <1024 bytes of JavaScript
- Source code is JSON (Lisp-0: functions, symbols, strings in same namespace)
- Full JavaScript interop
- Originally created for JS1K competition

### Notable Implementations

The repository includes implementations in unusual languages:
- **Bash**: Shell scripting
- **Make**: GNU Make
- **PostScript**: Printer language
- **SQL**: PostgreSQL PL/pgSQL
- **AWK**: Text processing language
- **VHDL**: Hardware description
- **Assembly**: x86-64

## Key Insights for Language Implementers

### What Makes Lisp Special

1. **Homoiconicity**: Code and data share the same structure (lists)
2. **Macros**: User-defined special forms, code that writes code
3. **Simple evaluation**: Only lists are "special" (first element determines behavior)
4. **Lexical scoping**: Closures capture their defining environment

### Recommended Implementation Order

1. **Steps 0-2**: Get basic REPL working (minimal viable interpreter)
2. **Steps 3-4**: Add environments and functions (usable language)
3. **Step 5**: TCO (required for idiomatic recursive Lisp)
4. **Step 6**: I/O and eval (practical language)
5. **Steps 7-8**: Quoting and macros (meta-programming)
6. **Steps 9-A**: Polish (exceptions, self-hosting)

### Common Pitfalls

- **Keywords**: Store with special prefix (e.g., `\u029e`) for easy identification
- **Variadic args**: Handle `&` in parameter lists
- **Environment lookup**: Must traverse outer chain
- **TCO**: Essential for recursive algorithms, requires loop transformation
- **Macro hygiene**: mal doesn't address this (like early Lisp)

## Relevance to Ziku

mal's approach offers several insights applicable to Ziku:

1. **Incremental development**: The step-by-step approach with tests at each stage is excellent for language development

2. **Self-hosting**: Achieving self-hosting is a strong validation of language completeness

3. **Test-driven**: The comprehensive test suite pattern could be adapted for Ziku's golden tests

4. **Environment model**: The simple linked environment structure is similar to what Ziku might need for lexical scoping

5. **Evaluation model**: While Ziku uses sequent calculus IR, the surface language evaluation could draw inspiration from mal's special form handling

## Sources

- [GitHub Repository](https://github.com/kanaka/mal)
- [Process Guide](https://github.com/kanaka/mal/blob/master/process/guide.md)
- [LambdaConf 2016 Presentation](https://kanaka.github.io/lambdaconf/)
- [C Implementation types.h](https://github.com/kanaka/mal/blob/master/impls/c.2/types.h)
- [Self-hosted Implementation](https://github.com/kanaka/mal/blob/master/impls/mal/stepA_mal.mal)
- [miniMAL Repository](https://github.com/kanaka/miniMAL)
