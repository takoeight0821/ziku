# Compilation to Scheme (Chez Scheme): Learning from Idris 2

## Overview

This document summarizes research on compiling functional languages to Scheme, with a focus on Idris 2's Chez Scheme backend. This is relevant to Ziku as a potential compilation target.

**Key References:**
- [Idris 2 Documentation - Chez Scheme Backend](https://idris2.readthedocs.io/en/latest/backends/chez.html)
- [Idris 2 Backend Cookbook](https://idris2.readthedocs.io/en/latest/backends/backend-cookbook.html)
- [Idris 2 GitHub Repository](https://github.com/idris-lang/Idris2)

## Why Chez Scheme?

### Advantages

1. **Mature Runtime System**: Chez Scheme provides a robust, well-engineered runtime with:
   - Generational garbage collection
   - Aggressive compiler optimizations (CP0 inlining)
   - Native code generation
   - Proper tail call optimization (required by Scheme spec)

2. **Performance**: According to [Edwin Brady](https://www.type-driven.org.uk/edwinb/why-is-idris-2-so-much-faster-than-idris-1.html):
   - Idris 2 self-compilation dropped from 700+ seconds to under 50 seconds
   - Chez can disable dynamic type checks for compiled code
   - Benefits from decades of optimization work

3. **Simplicity**: The IR maps naturally to S-expressions, requiring minimal translation

4. **Bootstrapping**: Generated Scheme code can bootstrap the compiler without requiring a binary distribution

### Comparison with Alternatives

| Target | Pros | Cons |
|--------|------|------|
| **Chez Scheme** | Fast compilation, excellent GC, proper TCO | Requires Chez installation |
| **Racket** | Good ecosystem, portable | Green threads (FFI caution) |
| **Gambit** | Compiles to C, portable | Slower compilation |
| **C (direct)** | Maximum control | Complex memory management, no native TCO |

## Idris 2 Compilation Pipeline

### Intermediate Representations

Idris 2 provides [4 IRs for backend implementers](https://idris2.readthedocs.io/en/latest/backends/backend-cookbook.html):

```
Source → TTImp → Core TT → CExp → [Named | LambdaLifted | ANF | VMDef]
                                          ↓
                                    Backend Code
```

1. **NamedDef**: Lambda calculus with names, closest to source
2. **LiftedDef**: Lambda-lifted, closures made explicit
3. **ANFDef**: Administrative Normal Form, all intermediates named
4. **VMDef**: Register-based virtual machine instructions

The Scheme backends use **NamedDef** (NamedCExp) because it maps directly to Scheme's structure.

### Key Translation Decisions

#### Data Representation

Constructors are represented as vectors with tags:
```scheme
; Constructor with tag and arguments
(vector tag arg1 arg2 ...)
```

Special optimizations for common types:
- Lists: Use native Scheme pairs (`cons`, `car`, `cdr`)
- Maybe: Use boxes
- Records: Direct vector construction

#### Closures

Lambda expressions translate directly:
```scheme
; Idris: \x => body
; Scheme:
(lambda (x) body)
```

Partial application creates closure objects tracking:
- Function reference
- Accumulated arguments
- Remaining arity

#### Lazy Evaluation

Idris uses explicit laziness via `Lazy` and `Inf`:
```scheme
; blodwen-lazy: wrap computation
; blodwen-force-lazy: evaluate

; With weak memoization (lazy=weakMemo directive):
; blodwen-delay-lazy: wrap with weak reference
```

### Primitive Operations

The `schOp` function maps primitives to Scheme:

| Idris Primitive | Scheme Implementation |
|-----------------|----------------------|
| `Add Int` | `(bs+ a b 63)` (bounded signed) |
| `Mul Int` | `(bs* a b 63)` |
| `StringLength` | `(string-length s)` |
| `Cast Int String` | `(number->string n)` |
| `DoubleFloor` | `(flfloor d)` |

### FFI (Foreign Function Interface)

Chez Scheme FFI uses `foreign-procedure`:
```scheme
(foreign-procedure "c_function_name" (int string) int)
```

The `%foreign` directive in Idris maps to backend-specific implementations:
```idris
%foreign "scheme:c_function_name"
myFunction : Int -> String -> Int
```

## Runtime Support (`support.ss`)

Idris 2's Chez runtime provides:

### Core Utilities
- **Numeric conversions**: `blodwen-toSignedInt`, `blodwen-toUnsignedInt`
- **String operations**: `string-concat`, `string-pack`, substring handling
- **Either types**: `either-left`, `either-right` via vectors

### Concurrency Primitives
- **Threads**: `blodwen-thread` with semaphore synchronization
- **Semaphores**: `blodwen-semaphore-post`, `blodwen-semaphore-wait`
- **Channels**: Message passing with timeout support
- **Barriers**: Multi-thread synchronization points
- **Futures**: `blodwen-await-future` for async computation

### Memory Management
- Buffer operations for 8/16/32/64-bit integers
- Finalizer registration for resource cleanup

## Compilation Output Structure

When compiling `main.idr`:
```
build/exec/
├── main           # Shell script launcher
└── main_app/
    ├── main.ss    # Generated Scheme source
    ├── main.so    # Compiled Scheme code
    └── *.so       # FFI shared libraries
```

The executable is relocatable if `_app` directory accompanies it.

## Alternative Approaches

### Lambda Lifting vs Closure Conversion

[Wikipedia: Lambda Lifting](https://en.wikipedia.org/wiki/Lambda_lifting)

**Lambda Lifting** (Thomas Johnsson, 1982):
- Eliminates free variables by adding parameters
- Moves local functions to global scope
- Requires call site adjustment
- Trades heap allocation for stack usage

**Closure Conversion**:
- Creates closure records capturing free variables
- Doesn't modify call sites
- Used by modern OCaml, Haskell (GHC)

Idris 2 provides **LiftedDef** IR for backends preferring lambda lifting.

### Defunctionalization

[Wikipedia: Defunctionalization](https://en.wikipedia.org/wiki/Defunctionalization)

Eliminates higher-order functions entirely:
- Each lambda gets a unique tag
- Single `apply` function dispatches on tag
- Useful for first-order targets

Not used by Scheme backends (Scheme supports first-class functions).

### Trampolining (for non-TCO targets)

When targeting languages without tail call optimization:

```python
# Trampoline loop
def trampoline(f):
    while callable(f):
        f = f()
    return f
```

Chez Scheme doesn't need this—it has native TCO.

## Other Scheme Compilation Examples

### Racket on Chez Scheme

[Rebuilding Racket on Chez Scheme](https://blog.racket-lang.org/2018/01/racket-on-chez-status.html)

Racket migrated from 200k lines of C to 150k lines of Scheme:
- Motivation: Maintainability over performance
- Result: Faster, easier to develop, better parallel GC
- Racket 8.0 (2021): Chez backend became default

### CHICKEN Scheme → C

[CHICKEN Compilation Process](https://wiki.call-cc.org/chicken-compilation-process)

Uses "Cheney on the M.T.A.":
- CPS transformation
- C stack as nursery heap
- Functions never return—call continuations instead
- GC copies live data when stack fills

### Gerbil Scheme (on Gambit)

[Gerbil Scheme](https://github.com/mighty-gerbils/gerbil)

- Built on Gambit (compiles to C)
- Full macro system (syntax-case)
- Module system similar to Racket
- Actor-oriented programming support

## Applying to Ziku (Implementation Notes)

The Scheme backend for Ziku has been implemented in `Ziku/Backend/Scheme.lean`.

### Pipeline

```
Surface.Expr → [Elaborate] → [Translate] → IR.Statement → [Scheme.compile] → .ss file
```

### Actual Translation Implementation

**Key insight**: The μ-reduction `⟨μα.s | c⟩ → s[c/α]` is implemented at compile-time using `let` bindings:

```scheme
; ⟨μα.s | c⟩ becomes:
(let ((α c)) <s>)

; ⟨v | μ̃x.s⟩ becomes:
(let ((x v)) <s>)
```

**Function application** (`ap` destructor):
```scheme
; ⟨f | ap(arg; cont)⟩
; f is (lambda (x) (lambda (k) body))
; Result: ((f arg) cont)
(lambda (f) ((f arg) cont))
```

**μ-arguments**: When function arguments are `μα.s` (not values), evaluate them first:
```scheme
; If arg is μα.s:
((lambda (α) s) (lambda (v) ((f v) cont)))
```

**Records**: Two representations:
1. Association lists: `(list (cons 'field1 val1) (cons 'field2 val2) ...)`
2. Dispatch functions (for recursive records): `(lambda (field) (case field ((f1) v1) ((f2) v2) ...))`

**Fixpoints** (`fix x. p`):
- Lambdas (`cocase`): Use `letrec` directly
- Records: Use dispatch function to handle recursive references

### Variable Capture Prevention

The destructor translation generates lambda expressions with parameter names. To avoid variable capture (where generated parameter names shadow user variables), we use:

1. **State monad (`GenM`)**: Threads a counter through translation to generate unique names
2. **Unique prefix (`%`)**: Generated names use `%` prefix which is invalid in Ziku identifiers but valid in Scheme

Example: Instead of `(lambda (f) ...)` which could shadow a user's `f` variable, we generate `(lambda (%fn0) ...)`.

### Known Limitations

1. **Performance**: The generated code has many nested lambdas and `let` bindings. Could be optimized with ANF transformation.

### Test Coverage

37 scheme tests covering:
- Literals, binary operations, conditionals
- Let bindings, lambdas, currying, composition
- Labels and goto (first-class control)
- Records and field access
- Recursive definitions (letrec, fix)
- Codata with lazy streams (fib, counter)
- Higher-order functions (Church numerals)

### Running the Backend

```bash
# Using the wrapper script (recommended)
./scripts/run-scheme.sh file.ziku              # Run from file
./scripts/run-scheme.sh -c "1 + 2"             # Run inline code
./scripts/run-scheme.sh -d file.ziku           # Debug mode (show generated code)
echo "1 + 2" | ./scripts/run-scheme.sh         # Run from stdin

# Manual compilation
.lake/build/bin/scheme-backend myfile.ziku > output.ss
scheme --script output.ss
```

### Minimal Runtime

The generated code includes a minimal runtime:
- `ziku-print-result`: Pretty-print values (handles booleans, records, functions)

No external runtime file needed - code is self-contained.

## Sources

### Official Documentation
- [Idris 2 Chez Scheme Backend](https://idris2.readthedocs.io/en/latest/backends/chez.html)
- [Idris 2 Backend Cookbook](https://idris2.readthedocs.io/en/latest/backends/backend-cookbook.html)
- [Chez Scheme Storage Management](https://cisco.github.io/ChezScheme/csug9.5/smgmt.html)

### Papers & Blog Posts
- [Idris 2: Quantitative Type Theory in Practice](https://arxiv.org/abs/2104.00480) - Edwin Brady, ECOOP 2021
- [Why is Idris 2 so much faster than Idris 1?](https://www.type-driven.org.uk/edwinb/why-is-idris-2-so-much-faster-than-idris-1.html) - Edwin Brady
- [Rebuilding Racket on Chez Scheme](https://dl.acm.org/doi/10.1145/3341642) - Flatt et al., ICFP 2019

### Source Code
- [Idris 2 Scheme Backends](https://github.com/idris-lang/Idris2/tree/main/src/Compiler/Scheme)
- [Idris 2 Chez Support](https://github.com/idris-lang/Idris2/blob/main/support/chez/support.ss)
- [Chez Scheme](https://github.com/cisco/ChezScheme)

### Related Implementations
- [CHICKEN Scheme Internals](https://www.more-magic.net/posts/internals-gc.html)
- [Gerbil Scheme](https://github.com/mighty-gerbils/gerbil)
- [Tutorial on Closure Conversion and Lambda Lifting](https://gist.github.com/jozefg/652f1d7407b7f0266ae9)
