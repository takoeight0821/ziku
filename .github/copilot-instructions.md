# Ziku - AI Coding Agent Instructions

## Project Overview
Ziku is an arithmetic expression evaluator with type inference, implemented in **Lean 4** (v4.26.0). It features a hand-written parser, environment-based evaluator, and foundational type system designed for future Hindley-Milner extension (let bindings, lambdas, polymorphism).

**Key design principle**: Proofs are first-class citizens. This is a theorem proving project with executable code.

## Architecture & File Organization

### Core Modules (Ziku/)
- [Syntax.lean](../Ziku/Syntax.lean): AST definition (`Expr` inductive), `size` for induction, `freeVars` for scoping
- [Parser.lean](../Ziku/Parser.lean): Hand-written parser using mutual recursion (parseExpr ↔ parseFactor ↔ parseAtom)
- [Type.lean](../Ziku/Type.lean): `Ty` (int | var) and `Subst` for future polymorphism
- [Infer.lean](../Ziku/Infer.lean): Type inference with `InferState`, `freshTyVar`, `unify` (currently Int-only)
- [Eval.lean](../Ziku/Eval.lean): Environment-based interpreter returning `Option Int` (handles division by zero)

### Proof Modules (Ziku/Proofs/)
- [Eval.lean](../Ziku/Proofs/Eval.lean): Evaluation correctness (`eval_lit`, `eval_add`, `eval_div_zero`)
- [Soundness.lean](../Ziku/Proofs/Soundness.lean): Type soundness (`infer_deterministic`, `infer_var_mem`)
- [Arithmetic.lean](../Ziku/Proofs/Arithmetic.lean), [Identities.lean](../Ziku/Proofs/Identities.lean): Algebraic properties

### Entry Points
- [Main.lean](../Main.lean): REPL using `partial def repl` (`:quit`/`:q` to exit)
- [Ziku.lean](../Ziku.lean): Library root importing all modules

## Critical Patterns

### Mutual Recursion for Precedence Parsing
Parser uses `mutual ... end` for operator precedence (* / > + -):
```lean
mutual
  partial def parseAtom : Parser Expr := ...  -- literals, vars, parens
  partial def parseFactor : Parser Expr := ... -- handles * /
  partial def parseExpr : Parser Expr := ...   -- handles + -
end
```
**Always use this structure when adding operators**. See [Parser.lean](../Ziku/Parser.lean#L55-L113) for reference.

### Partial Functions
Use `partial def` for recursion without termination proofs (parser, REPL). For provable functions (evaluator, type inference), provide structural recursion or well-founded measure.

### Theorem Naming Convention
- `eval_*` for evaluation properties ([Eval.lean](../Ziku/Proofs/Eval.lean))
- `infer_*` for type inference properties ([Soundness.lean](../Ziku/Proofs/Soundness.lean))
- Parameters: `env`, `e`/`e1`/`e2`, `v`/`v1`/`v2`, hypotheses `h`/`h1`/`h2`

### Error Handling
- Parser: `Except String` (position-aware errors)
- Evaluator: `Option Int` (returns `none` for undefined vars, division by zero)
- Type inference: `Option (Ty × Subst × InferState)`

## Build & Development Workflow

```bash
# Build executable and library
lake build

# Run REPL
./.lake/build/bin/ziku

# Clean build artifacts
lake clean

# Update dependencies
lake update
```

**No test framework configured** - verification is via formal proofs in `Ziku/Proofs/`.

## Adding New Features

### To Add a New Operator (e.g., modulo)
1. Add constructor to `Expr` in [Syntax.lean](../Ziku/Syntax.lean#L3-L10)
2. Update `Expr.size` and `Expr.freeVars`
3. Add parsing in [Parser.lean](../Ziku/Parser.lean) (choose precedence level)
4. Add evaluation case in [Eval.lean](../Ziku/Eval.lean#L7-L28)
5. Add type inference case in [Infer.lean](../Ziku/Infer.lean#L32-L49)
6. **Prove correctness** in [Proofs/Eval.lean](../Ziku/Proofs/Eval.lean)

### To Add Variables/Let Bindings
1. Extend parser to handle `let x = e1 in e2` syntax
2. Add `Expr.let` constructor
3. Update `freeVars` to exclude bound variables
4. Extend `Env` handling in evaluator
5. Update `TyEnv` in type inference
6. **Prove substitution lemmas** for new binding constructs

## Type System Design Notes
Current implementation is Int-only, but infrastructure supports polymorphism:
- `Ty.var n` for type variables (currently unused)
- `Subst` for unification substitutions
- `InferState` tracks fresh variable generation
- `unify` is basic but extensible

See author's research on [sequent calculus](../docs/research/grokking-the-sequent-calculus.md) and [Malgo compiler](../docs/research/malgo.md) for architectural inspiration.

## Commit Convention
Use [Conventional Commits](https://www.conventionalcommits.org/): `feat:`, `fix:`, `docs:`, `refactor:`, `test:` (see [CLAUDE.md](../CLAUDE.md))
