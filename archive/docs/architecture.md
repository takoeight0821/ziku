# Ziku Architecture

This document describes the architecture of the Ziku programming language implementation.

## Directory Structure

```
Ziku/
├── Syntax.lean         # Shared types: SourcePos, Ident, Lit, BinOp, Builtin, Pat, Ty
├── Surface/
│   └── Syntax.lean     # Surface AST with label/goto
├── IR/
│   ├── Syntax.lean     # Sequent calculus IR (Producer, Consumer, Statement)
│   └── Eval.lean       # IR evaluator with μ/μ̃-reduction and builtin evaluation
├── Backend/
│   └── Scheme.lean     # Scheme code generator (CPS translation)
├── Translate.lean      # Surface → IR translation (including builtin detection)
├── Lexer.lean          # Hand-written lexer with UTF-8 support
├── Parser.lean         # Hand-written recursive descent parser
├── Type.lean           # Type utilities: Subst, Scheme
├── Infer.lean          # HM type inference (including builtin type checking)
├── Elaborate.lean      # Codata elaboration
└── Proofs/             # Lean proofs (Arithmetic, Eval, Identities, Soundness)
```

## Pipeline

```
Source → [Parse] → Surface.Expr → [Translate] → IR.Statement → [Eval]
                        ↓                              ↓
                   [Elaborate] → [Infer]          [Scheme Backend]
```

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
