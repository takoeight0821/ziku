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
# Build Docker image (one-time setup, ~2 minutes)
docker build -t ziku .

# Run tests
docker run --rm ziku lake test

# Run REPL
docker run --rm -it ziku lake exe ziku

# Build project
docker run --rm ziku lake build

# Run Chez Scheme
docker run --rm -it ziku scheme
```

### Native (only if Docker is unavailable)

Requires Lean 4 and Chez Scheme installed locally.

```bash
lake build              # Build everything
lake test               # Run golden tests (parser, eval, infer, ir-eval)
lake exe ziku           # Run REPL
```

## Dependency Management

### Automated Updates

Ziku uses a hybrid approach combining Renovate and custom GitHub Actions workflows for comprehensive dependency management:

**Renovate** (weekly, Mondays 9:00 UTC):
- GitHub Actions (with SHA digest pinning for supply chain security)
- Docker base images (`ubuntu:24.04`)
- Git submodules

**GitHub Actions Workflow** (weekly, Mondays 9:00 UTC):
- Lean toolchain (`lean-toolchain` file)
- Lake dependencies (`lake-manifest.json` with build/test validation)
- Elan installer version (Dockerfile ARG)

### How Renovate Runs

Renovate runs via self-hosted GitHub Actions workflow (`.github/workflows/renovate.yml`):
- **Schedule**: Weekly on Mondays at 9:00 UTC
- **Authentication**: GitHub App with repository secrets (`RENOVATE_APP_ID`, `RENOVATE_APP_PRIVATE_KEY`)
- **Configuration**: `.github/renovate.json`
- **Features**: Digest pinning for GitHub Actions, grouped updates, commit signing

**To manually trigger**: Go to Actions tab → Renovate workflow → Run workflow

**Creating the GitHub App**: Run `./scripts/create-github-app.sh` (requires GitHub CLI)

### Dependency Strategy

**Elan installer**: Pinned to specific git tag (e.g., `v4.1.2`) via Dockerfile ARG directive
- Updated automatically via GitHub Actions (weekly checks)
- Location: `Dockerfile` ARG ELAN_VERSION

**APT packages**: Not version-pinned (security-first approach)
- Rationale: Ubuntu 24.04 LTS provides security updates + API stability until 2029
- Trade-off: Reproducibility vs security updates
- Override: Use `docker build --build-arg` for pinned builds if needed

**Lean toolchain**: Pinned via `lean-toolchain` file (e.g., `leanprover/lean4:v4.26.0`)
- Updated automatically via GitHub Actions (weekly checks)

**Lake dependencies**: Managed by `lake-manifest.json`
- Updated automatically with build/test validation before PR creation

### Manual Updates

To update dependencies manually:

```bash
# Update Lean toolchain
# 1. Edit lean-toolchain file with desired version
# 2. Run: docker build --no-cache -t ziku .

# Update elan version
# 1. Edit ARG ELAN_VERSION in Dockerfile
# 2. Run: docker build --no-cache -t ziku .

# Update Lake dependencies
lake update && lake build && lake test
```

### Rollback Procedures

**If elan update breaks builds:**
1. Revert Dockerfile: `git checkout HEAD~1 Dockerfile`
2. Pin to last working version
3. Open issue on leanprover/elan repository

**If Renovate creates problematic PRs:**
1. Close PR with comment explaining issue
2. Add to `ignoreDeps` in `.github/renovate.json`
3. Pin version manually if needed

**If Lean toolchain update fails tests:**
1. Close auto-generated PR
2. Investigate test failures
3. Wait for next Lean release or report upstream

## Architecture

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

### Pipeline

```
Source → [Parse] → Surface.Expr → [Translate] → IR.Statement → [Eval]
                        ↓                              ↓
                   [Elaborate] → [Infer]          [Scheme Backend]
```

### Key Types

**Surface Language (Ziku.Expr)**:

- `lit`, `var`, `hash` (#), `binOp`, `unaryOp`
- `lam`, `app`, `let_`, `letRec`, `if_`
- `match_`, `codata`, `field`, `record`
- `label`, `goto` - control flow primitives
- `ann` - type annotation

**Sequent Calculus IR**:

- `Producer`: `var`, `lit`, `mu`, `cocase`, `record`, `fix`, `dataCon`
- `Consumer`: `covar`, `muTilde`, `case`, `destructor`
- `Statement`: `cut`, `binOp`, `ifz`, `call`, `builtin`

**Built-in Functions** (detected during type inference/translation):

- String: `strLen`, `strAt`, `strSub`, `strToInt`, `intToStr`
- Rune: `intToRune`, `runeToInt`, `runeToStr`

**Types**: `Int`, `Float`, `String`, `Rune`, `Bool`, `Unit` (note: `Rune` replaces `Char` for Unicode code points)

### Core Design

**Surface Language**:

- **Pattern matching** (`|` clauses): destructs data types
  - Supports nested patterns: `Cons(MNum(a), rest)` compiles to nested case expressions
  - Literal patterns in constructor args: `Cons(42, _)`
  - Uses join points (`mu`/`covar`) for failure handling
- **Copattern matching** (`{}` blocks): constructs codata types
- **`#`**: represents the object being defined (like `this`/`self`)
- **`label name { body }`**: creates a control point
- **`goto(value, name)`**: jumps to label with value

**IR (λμμ̃-calculus)**:

- **`μα.s`**: producer abstraction, captures continuation α
- **`μ̃x.s`**: consumer abstraction, binds value x
- **`⟨p | c⟩`**: cut, connects producer p with consumer c

### Translation Rules (Grokking the Sequent Calculus)

```
⟦x⟧                     =  x
⟦⌜n⌝⟧                   =  ⌜n⌝
⟦t₁ ⊙ t₂⟧               =  μα. ⊙(⟦t₁⟧, ⟦t₂⟧; α)
⟦if t₁ then t₂ else t₃⟧ =  μα.ifz(⟦t₁⟧, ⟨⟦t₂⟧ | α⟩, ⟨⟦t₃⟧ | α⟩)
⟦let x = t₁ in t₂⟧      =  μα.⟨⟦t₁⟧ | μ̃x.⟨⟦t₂⟧ | α⟩⟩
⟦λx.t⟧                  =  cocase {ap(x; α) ⇒ ⟨⟦t⟧ | α⟩}
⟦t₁ t₂⟧                 =  μα.⟨⟦t₁⟧ | ap(⟦t₂⟧; α)⟩
⟦label α {t}⟧           =  μα.⟨⟦t⟧ | α⟩
⟦goto(t; α)⟧            =  μβ.⟨⟦t⟧ | α⟩  (β fresh)
```

### IR Reduction Rules

```
⟨μα.s | c̄⟩    ⊲  s[c̄/α]     (μ-reduction)
⟨v̄ | μ̃x.s⟩    ⊲  s[v̄/x]     (μ̃-reduction, v is value)
```

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

## Conventions

- Use conventional commit format for commit messages
- The parser is hand-written due to Std.Internal.Parsec API issues
- Use `partial` for recursive functions where termination is hard to prove
  - **When to use `partial`**: For evaluators, interpreters, and complex mutual recursions where termination proof is impractical
  - **Alternatives to consider**:
    - Add `termination_by` clause with explicit measure (e.g., `sizeOf`, custom metrics)
    - Use fuel parameter (`fuel : Nat`) to bound recursion depth
    - Implement step-based execution with explicit state machine
    - Refactor mutual recursion into unified type + single recursive function
  - **Trade-offs**: `partial def` enables practical implementation but cannot be used in proofs; choose based on whether the function needs to be used in formal verification
- Source positions are tracked throughout AST for error reporting
- Use explicit function calls (e.g., `Producer.substVar x p prod`) instead of dot notation in mutual recursive functions to avoid argument order issues

## Hints

- `rm` is denied for safety, use `trash` command instead
- If you want to try simpler case, you should add it as golden test
