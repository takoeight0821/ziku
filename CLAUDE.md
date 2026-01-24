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

**IMPORTANT: Use Docker for all builds and tests to ensure consistent environments across development and CI.**

### Docker (Recommended - no local dependencies required)

```bash
# Build Docker image (one-time setup)
docker build -t ziku .

# Run tests
docker run --rm ziku nix develop --command lake test

# Run REPL
docker run --rm -it ziku nix develop --command lake exe ziku

# Build project
docker run --rm ziku nix develop --command lake build
```

### Native (only if Docker is unavailable)

Requires Lean 4 and Chez Scheme installed locally.

```bash
lake build              # Build everything
lake test               # Run golden tests (parser, eval, infer, ir-eval)
lake exe ziku           # Run REPL
```

## Dependency Management

See [README.md#for-developers](README.md#for-developers) for detailed dependency management setup.

Quick reference:
- Nix flakes (`flake.nix`, `flake.lock`) for reproducible builds
- Renovate for automated dependency updates (weekly)
- Lean toolchain pinned via `lean-toolchain`
- Lake dependencies managed by `lake-manifest.json`

## Architecture

See [docs/architecture.md](docs/architecture.md) for detailed architecture.

Key points:
- Surface language → IR translation via `Translate.lean`
- IR based on λμμ̃-calculus from "Grokking the Sequent Calculus"
- Scheme backend for code generation
- Use `/sequent-calculus` skill for translation rules and reduction semantics

## Testing

Golden tests in `tests/golden/`:

- `parser/success/`: Parser success tests (.ziku -> .golden)
- `parser/error/`: Parser error tests (expected parse failures)
- `infer/success/`: Type inference success tests
- `infer/error/`: Type inference error tests
- `ir-eval/success/`: IR evaluation tests (via translation)

Tests are auto-discovered from `.ziku` files. Add new test by:

1. Create `tests/golden/{category}/{success|error}/{name}.ziku`
2. Run `lake test` to auto-generate `.golden` file

### Test Execution Options

```bash
# Run all tests
lake test

# Run specific category only (faster feedback during development)
lake test -- parser              # Parser tests only
lake test -- infer               # Type inference tests only
lake test -- parser infer        # Multiple categories

# Parallel execution (recommended for full test runs)
make -j4 test-parallel           # Run all categories in parallel
make -j4 test-fast               # Run fast tests only (parser, infer, truncate, big-step)
make -j4 test-medium             # Run fast + medium tests

# Show available categories
lake test -- --help
```

Available categories: `truncate`, `big-step`, `parser`, `infer`, `ir-eval`, `ir-eval-big-step`, `emit-translate`, `emit-scheme`, `scheme-only`, `consistency`, `big-step-consistency`, `io`

## Conventions

- Use conventional commit format for commit messages
- The parser is hand-written due to Std.Internal.Parsec API issues
- Use `partial` for recursive functions where termination is hard to prove
  - **Alternatives to consider**: `termination_by` clause, fuel parameter, step-based execution
  - **Trade-offs**: `partial def` enables practical implementation but cannot be used in proofs
- Source positions are tracked throughout AST for error reporting
- Use explicit function calls (e.g., `Producer.substVar x p prod`) instead of dot notation in mutual recursive functions

## Verification Checklist

After making code changes, verify:

1. **Build succeeds**: `docker run --rm ziku nix develop --command lake build`
2. **All tests pass**: `docker run --rm ziku nix develop --command lake test`
3. **New features have tests**: Add corresponding golden tests in `tests/golden/`
4. **Proofs are complete**: If `Proofs/` was modified, ensure no `sorry` remains

## Hints

- `rm` is denied for safety, use `trash` command instead
- If you want to try simpler case, you should add it as golden test
- If you write a plan, please add the date at the top of the file
