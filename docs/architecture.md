# Ziku Architecture

This document describes the architecture of the Ziku programming language implementation.

## Directory Structure

```
Ziku/
├── Syntax.lean               # Shared types (SourcePos, Ident, Lit, BinOp, Builtin, Pat, Ty) and the surface AST (Expr)
├── IR/
│   ├── Syntax.lean           # Sequent calculus IR (Producer, Consumer, Statement)
│   ├── Eval.lean             # Small-step IR evaluator with μ/μ̃-reduction and builtin evaluation
│   ├── BigStepEval.lean      # Big-step IR interpreter tuned for execution speed
│   ├── Focusing.lean         # Static focusing: lifts non-values out of value positions
│   └── Simplify.lean         # Administrative redex elimination (safe μ/μ̃-reductions)
├── Backend/
│   └── Scheme.lean           # Scheme code generator (CPS translation)
├── Translate.lean            # Surface → IR translation (including builtin detection)
├── Lexer.lean                # Hand-written lexer with UTF-8 support
├── Parser.lean               # Hand-written recursive descent parser
├── Type.lean                 # Type utilities: Subst, Scheme
├── Infer.lean                # HM type inference (including builtin type checking)
├── Elaborate.lean            # Codata elaboration (copatterns → records and lambdas)
├── Builtins.lean             # Shared utilities for built-in functions used by inference and translation
├── FreshName.lean            # Hygienic names for compiler-generated variables
├── Import.lean               # Module system resolution
├── Path.lean                 # Import path resolution
├── Soundness.lean            # Type safety theorems and proofs of their basic cases
└── Proofs/
    ├── Arithmetic.lean       # Arithmetic properties (placeholder)
    ├── Eval.lean             # Evaluation correctness (placeholder)
    ├── Identities.lean       # Algebraic identities (placeholder)
    ├── Path.lean             # Properties of path resolution
    ├── Soundness.lean        # Type soundness lemmas
    └── IR/
        ├── Values.lean       # Values as inductive relations
        ├── Substitution.lean # Substitution as inductive relations
        ├── Semantics.lean    # Small-step operational semantics as a relation
        └── Evaluation.lean   # Multi-step evaluation properties
```

## Pipeline

The CLI (`Main.lean`) parses the source once, resolves the types of its
imports (an import error stops every mode), and then takes one of these paths:

```
Source
  │ parse
  ▼
Expr                     resolveImportTypes → import type map
  ├──(--parse)──▶ printed Expr
  ├──(--infer)──▶ runInfer ──▶ Ty    uses the import type map; codata is elaborated inside Infer
  │
  │ expandImports
  ▼
Expr
  │ elaborateAll           codata → records and lambdas
  ▼
Expr
  │ translateToStatement   Translate, then IR.Focusing.focus
  ▼
IR.Statement
  ├──(--translate)────────▶ printed IR
  ├──(--scheme)───────────▶ Backend.Scheme.compile   IR.simplify, then code generation
  ├──(--eval)─────────────▶ IR.eval                  small-step
  └──(--eval --big-step)──▶ IR.BigStepEval.eval      big-step
```

The REPL skips `expandImports` and starts from `elaborateAll`.

## Key Types

### Surface Language (Ziku.Expr)

- `lit`, `var`, `hash` (#), `binOp`, `unaryOp`
- `lam`, `app`, `let_`, `letRec`, `if_`
- `match_`, `codata`, `field`, `record`
- `label`, `goto` - control flow primitives
- `ann` - type annotation

### Sequent Calculus IR

- `Producer`: `var`, `lit`, `mu`, `cocase`, `record`, `fix`, `dataCon`
- `Consumer`: `covar`, `muTilde`, `case`, `destructor`
- `Statement`: `cut`, `binOp`, `ifz`, `call`, `builtin`

### Built-in Functions

Detected during type inference/translation:

- String: `strLen`, `strAt`, `strSub`, `strToInt`, `intToStr`
- Rune: `intToRune`, `runeToInt`, `runeToStr`

### Types

`Int`, `Float`, `String`, `Rune`, `Bool`, `Unit` (note: `Rune` replaces `Char` for Unicode code points)

## Core Design

### Surface Language

- **Pattern matching** (`|` clauses): destructs data types
  - Supports nested patterns: `Cons(MNum(a), rest)` compiles to nested case expressions
  - Literal patterns in constructor args: `Cons(42, _)`
  - Uses join points (`mu`/`covar`) for failure handling
- **Copattern matching** (`{}` blocks): constructs codata types
- **`#`**: represents the object being defined (like `this`/`self`)
- **`label name { body }`**: creates a control point
- **`goto(value, name)`**: jumps to label with value

### IR (λμμ̃-calculus)

- **`μα.s`**: producer abstraction, captures continuation α
- **`μ̃x.s`**: consumer abstraction, binds value x
- **`⟨p | c⟩`**: cut, connects producer p with consumer c

For translation rules and reduction semantics, see the `/sequent-calculus` skill or [docs/research/grokking-the-sequent-calculus.md](research/grokking-the-sequent-calculus.md).
