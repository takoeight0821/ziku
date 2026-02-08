# CLAUDE.md

This file provides guidance to Claude Code (claude.ai/code) when working with code in this repository.

## Project Overview

Ziku is a programming language implementation in Lean 4 featuring:

- **Duality-aware design**: explicit data/codata symmetry
- **Sequent calculus IR**: λμμ̃-calculus based intermediate representation
- **Surface/IR separation**: user-friendly surface syntax translated to sequent calculus
- **Copattern matching**: for codata construction using `#` (self-reference)
- **Hindley-Milner type inference** with let-polymorphism

## Build Commands

### Docker via mise (Recommended)

```bash
mise run docker:build            # Build Docker image
mise run docker:test             # Run all tests (builds image automatically)
mise run docker:test:category infer  # Run specific test category
mise run docker:build-check      # Check build succeeds
mise run docker:repl             # Start REPL
mise run docker:infer tests/golden/infer/success/let_simple.ziku  # Infer type of a file
mise run docker:run <phase> <expr-or-file>  # Quick test of expression or file
```

### Native

Requires Lean 4 and Chez Scheme installed locally.

```bash
lake build              # Build everything
lake test               # Run golden tests (parser, eval, infer, ir-eval)
lake exe ziku           # Run REPL
make -j4 test-parallel  # Run tests in parallel
```

## Dependency Management

See [README.md#for-developers](README.md#for-developers) for detailed dependency management setup.

Quick reference:
- Renovate for automated dependency updates (weekly)
- Lean toolchain pinned via `lean-toolchain`
- Lake dependencies managed by `lake-manifest.json`
- Docker uses Debian trixie-slim with apt packages

## Architecture

See [docs/architecture.md](docs/architecture.md) for detailed architecture.

Key points:
- Surface language → IR translation via `Translate.lean`
- IR based on λμμ̃-calculus from "Grokking the Sequent Calculus"
- Scheme backend for code generation
- Use `/sequent-calculus` skill for translation rules and reduction semantics

### Key Modules

**Core pipeline** (in execution order):
- `Lexer.lean` - Tokenization, forbids `#` in user identifiers
- `Parser.lean` - Hand-written parser (Parsec API issues)
- `Elaborate.lean` - Copattern desugaring to records/lambdas
  - Uses `ElabM := StateT Nat (Except ElaborateError)` for fresh names
  - Public API: `elaborateAll` wraps with `.run' 0`
- `Infer.lean` - Hindley-Milner type inference with let-polymorphism
  - Calls `(elaborate pos clauses).run' 0` for codata elaboration
- `Translate.lean` - Surface → sequent calculus IR
- `Backend/Scheme.lean` - Code generation (`#` → `_hash_`)

**Supporting modules**:
- `FreshName.lean` - Hygienic name constants (`#` prefix system)
  - All compiler-generated names: `#α0`, `#wild`, `#lit_int_42`
  - Central constants: `wildCon`, `varCon`, `litIntPrefix`
- `Syntax.lean` - AST definitions
- `Type.lean` - Type representation
- `Import.lean` - Module system resolution

## Testing

Golden tests in `tests/golden/`:

- `parser/success/`: Parser success tests (.ziku -> .golden)
- `parser/error/`: Parser error tests (expected parse failures)
- `infer/success/`: Type inference success tests
- `infer/error/`: Type inference error tests
- `ir-eval/success/`: IR evaluation tests (via translation)

Tests are auto-discovered from `.ziku` files.

### Test Execution Options

```bash
# Docker (recommended - no local dependencies)
mise run docker:test                     # Run all tests
mise run docker:test:category infer      # Run specific category
mise run docker:test:category parser     # Parser tests only

# Native (requires Lean 4 + Chez Scheme)
lake test                                # Run all tests
lake test -- parser                      # Parser tests only
lake test -- infer                       # Type inference tests only
lake test -- parser infer                # Multiple categories

# Parallel execution (native, recommended for full test runs)
make -j4 test-parallel           # Run all categories in parallel
make -j4 test-fast               # Run fast tests only (parser, infer, truncate, big-step)
make -j4 test-medium             # Run fast + medium tests
```

Available categories: `truncate`, `big-step`, `parser`, `infer`, `ir-eval`, `ir-eval-big-step`, `emit-translate`, `emit-scheme`, `scheme-only`, `consistency`, `big-step-consistency`, `io`

### Golden Test Workflow

**Creating new tests**:
1. Write `.ziku` file in appropriate category (e.g., `tests/golden/infer/success/my_test.ziku`)
2. Run via Docker to generate output: `mise run docker:run <phase> tests/golden/.../my_test.ziku`
3. Copy expected output to `.golden` file: `tests/golden/infer/success/my_test.golden`
4. Run category tests: `mise run docker:test:category infer`

**Moving tests**:
- Moving between `error/` and `success/` requires creating new `.golden` files
- Golden files are not automatically regenerated on move

## Conventions

- Use conventional commit format for commit messages
- The parser is hand-written due to Std.Internal.Parsec API issues

## Verification Checklist

After making code changes, verify:

1. **Build succeeds**: `mise run docker:build-check`
2. **All tests pass**: `mise run docker:test`
3. **New features have tests**

## Hints

### General
- `rm` is denied for safety, use `trash` command instead
- If you want to try simpler case, you should add it as golden test
- If you write a plan, please add the date at the top of the file

### Type System (Infer.lean)
- **Variable numbering shifts**: Adding `freshTyVar` calls shifts `_tN` numbering in golden tests. Always update golden files after constraint generation changes.
- **ElabM pattern**: `Elaborate.lean` returns `ElabM Expr`. Callers (e.g., `Infer.lean`) must use `(elaborate pos clauses).run' 0`.

### Hygienic Names (FreshName.lean)
- **`#` prefix system**: All compiler-generated variables use `#` prefix (e.g., `#α0`, `#wild`, `#lit_int_42`)
- The `#` char is invalid in user identifiers but handled by Scheme backend's `mangleIdent` (`#` → `_hash_`)
- Import `Ziku.FreshName` for constants like `wildCon`, `varCon`, `litIntPrefix`

### Docker/Build
- Docker rebuilds on every `mise run docker:*` (depends on `docker:build`)
- Tests copy from host `tests/` dir, so golden file changes need image rebuild
- Build is cached if only test files change (Docker layer optimization)
