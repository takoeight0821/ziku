# CLAUDE.md

This file provides guidance to Claude Code (claude.ai/code) when working with code in this repository.

## Project Overview

Ziku is a programming language implementation in Lean 4 featuring:

- **Duality-aware design**: explicit data/codata symmetry
- **Sequent calculus foundation**: producers and consumers as first-class concepts
- **Copattern matching**: for codata construction using `#` (self-reference)
- **Hindley-Milner type inference** with let-polymorphism

## Build Commands

```bash
lake build              # Build everything
lake test               # Run golden tests (parser, eval, infer)
lake exe ziku           # Run REPL
```

## Architecture

```
Ziku/
├── Syntax.lean    # Complete AST: Expr, Pat, Ty, Decl, Accessor, Copattern
├── Lexer.lean     # Hand-written lexer with UTF-8 support
├── Parser.lean    # Hand-written recursive descent parser
├── Type.lean      # Type utilities: Subst, Scheme, substitution application
├── Infer.lean     # HM type inference with InferM monad
├── Eval.lean      # Environment-based interpreter
└── Proofs/        # Lean proofs (Arithmetic, Eval, Identities, Soundness)
```

### Key Types

- `Expr`: Expressions include `lit`, `var`, `hash` (#), `binOp`, `lam`, `app`, `let_`, `letRec`, `match_`, `codata`, `field`, `record`, `if_`, `cut`, `mu`
- `Ty`: Types include `var`, `con`, `app`, `arrow`, `forall_`, `record`
- `Pat`: Patterns for destructuring data
- `Copattern`: List of `Accessor` (.field or (arg)) for codata construction
- `InferM`: StateT InferState (Except TypeError) for type inference

### Core Design

The language distinguishes:

- **Pattern matching** (`|` clauses): destructs data types
- **Copattern matching** (`{}` blocks): constructs codata types
- **`#`**: represents the object being defined (like `this`/`self`)
- **`cut <producer | consumer>`**: sequent calculus cut
- **`mu k => e`**: continuation binding

## Testing

Golden tests in `tests/golden/`:

- `parser/`: Parser output tests (.ziku -> .golden)
- `eval/`: Evaluation tests
- `infer/`: Type inference tests

Tests are listed in `tests/GoldenTest.lean`. Add new test by:

1. Create `tests/golden/{category}/{name}.ziku`
2. Add test name to corresponding list in `GoldenTest.lean`
3. Run `lake test` to auto-generate `.golden` file

## Conventions

- Use conventional commit format for commit messages
- The parser is hand-written due to Std.Internal.Parsec API issues
- Use `partial` for recursive functions where termination is hard to prove
- Source positions are tracked throughout AST for error reporting
