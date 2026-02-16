# Type Inference: A Comprehensive Survey

## Overview

Type inference is the automatic detection of types in a programming language without requiring explicit type annotations. It ranges from simple local inference to complete global inference systems that can determine the most general (principal) type for any well-typed expression.

## Historical Background

- **1958**: Haskell Curry and Robert Feys devised the type inference algorithm for the simply typed lambda calculus
- **1969**: J. Roger Hindley extended this work and proved their algorithm always infers the most general type
- **1978**: Robin Milner independently provided an equivalent algorithm (Algorithm W)
- **1982**: Luis Damas proved Milner's algorithm is complete
- **1998**: Lee and Yi formally proved Algorithm M (the "folklore" top-down algorithm)

---

## Part 1: Hindley-Milner Type System

### Core Concepts

The Hindley-Milner (HM) type system is a classical type system for the lambda calculus with parametric polymorphism. Key properties:

- **Completeness**: Can infer types for all well-typed programs
- **Principal Types**: Always infers the most general type
- **Decidability**: Type inference terminates for all inputs
- **No Annotations Required**: Works without programmer-supplied type hints

### Type Language

**MonoTypes (τ)**: Concrete types without quantifiers
```
τ ::= α           -- type variable
    | T τ₁...τₙ   -- type constructor application
```

**PolyTypes (σ)**: Type schemes with universal quantification
```
σ ::= τ | ∀α.σ
```

### Key Operations

1. **Generalization**: Converting τ to σ by quantifying free type variables
   ```
   gen(Γ, τ) = ∀(FV(τ) - FV(Γ)).τ
   ```

2. **Instantiation**: Converting σ to τ with fresh type variables
   ```
   inst(∀α₁...αₙ.τ) = τ[α₁ ↦ β₁, ..., αₙ ↦ βₙ]  (fresh βᵢ)
   ```

3. **Unification**: Finding a substitution that makes two types equal
   ```
   unify(τ₁, τ₂) = S such that S(τ₁) = S(τ₂)
   ```

### Let-Polymorphism

HM restricts polymorphism to let-bindings only (not lambda-bindings):

```ml
let id = λx.x in         -- id : ∀α.α → α
  (id 1, id true)        -- works: different instantiations
```

vs.

```ml
(λid. (id 1, id true))   -- fails: id must have single type
  (λx.x)
```

This restriction is essential for decidability—allowing polymorphism for λ-bound variables leads to System F, where type inference is undecidable.

---

## Part 2: Classic Inference Algorithms

### Algorithm W (Bottom-Up, Functional)

The most well-known algorithm, characterized by:
- **Pure/functional**: No side effects, threads substitutions explicitly
- **Bottom-up**: Infers types from subexpressions upward
- **Well-proven**: Easiest to prove correct

```
W(Γ, e) → (S, τ)

W(Γ, x) = (∅, inst(Γ(x)))

W(Γ, λx.e) =
  let α = fresh()
      (S, τ) = W(Γ[x↦α], e)
  in (S, S(α) → τ)

W(Γ, e₁ e₂) =
  let (S₁, τ₁) = W(Γ, e₁)
      (S₂, τ₂) = W(S₁(Γ), e₂)
      α = fresh()
      S₃ = unify(S₂(τ₁), τ₂ → α)
  in (S₃ ∘ S₂ ∘ S₁, S₃(α))

W(Γ, let x = e₁ in e₂) =
  let (S₁, τ₁) = W(Γ, e₁)
      σ = gen(S₁(Γ), τ₁)
      (S₂, τ₂) = W(S₁(Γ)[x↦σ], e₂)
  in (S₂ ∘ S₁, τ₂)
```

### Algorithm J (Imperative)

Uses union-find data structure with mutable state:
- **More efficient**: Single global substitution
- **Harder to prove**: Formal correctness less obvious
- **Common in practice**: Used in real compilers

Key idea: Type variables maintain forwarded pointers; `find()` resolves to root equivalence class.

### Algorithm M (Top-Down)

The "folklore" algorithm, formally proven in 1998:
- **Top-down**: Takes expected type as parameter
- **Earlier error detection**: Stops faster on ill-typed programs
- **Better error messages**: Context-sensitive inference

```
M(Γ, e, τ_expected) → S
```

### Comparison

| Aspect | Algorithm W | Algorithm M | Algorithm J |
|--------|-------------|-------------|-------------|
| Direction | Bottom-up | Top-down | Bottom-up |
| Side effects | Pure | Context-sensitive | Imperative |
| Error detection | Later | Earlier | Similar to W |
| Efficiency | Less efficient | Varies | More efficient |
| Use case | Theory/proofs | Better errors | Real compilers |

---

## Part 3: Unification

### Robinson's Unification Algorithm (1965)

```
unify(τ₁, τ₂) =
  match (τ₁, τ₂) with
  | (α, τ) | (τ, α) →
      if α ∈ FV(τ) then fail "occurs check"
      else [α ↦ τ]
  | (T τ₁...τₙ, T σ₁...σₙ) →
      unify_many([(τ₁,σ₁),...,(τₙ,σₙ)])
  | (T ..., T' ...) where T ≠ T' → fail "mismatch"
```

### The Occurs Check

Prevents infinite types by checking if a variable appears in a type before unifying:

```
occurs_check(α, τ) = α ∈ FV(τ)
```

Without this check, `α = α → α` would create a cycle.

### Properties

- **Most General Unifier (MGU)**: The computed substitution is the most general one
- **Termination**: Always terminates (types are finite)
- **Principal Types**: Leads to inference of most general types

---

## Part 4: Bidirectional Type Checking

### Overview

Bidirectional typing combines two modes:
- **Checking (⇐)**: Verify that expression has a known type
- **Synthesis (⇒)**: Infer type from expression structure

### Benefits

1. **Supports undecidable features**: Can handle features where full inference is impossible
2. **Reduces annotation burden**: Only needs annotations at specific points
3. **Better error locality**: Errors are reported closer to their source

### Core Rules

```
Γ ⊢ e ⇒ A     (synthesis: infer A from e)
Γ ⊢ e ⇐ A     (checking: check e against A)

-- Subsumption (mode switch)
Γ ⊢ e ⇒ A    A <: B
─────────────────────
Γ ⊢ e ⇐ B

-- Annotation
Γ ⊢ e ⇐ A
─────────────────
Γ ⊢ (e : A) ⇒ A

-- Lambda (checking mode)
Γ, x:A ⊢ e ⇐ B
──────────────────────
Γ ⊢ λx.e ⇐ A → B

-- Application (synthesis mode)
Γ ⊢ e₁ ⇒ A → B    Γ ⊢ e₂ ⇐ A
─────────────────────────────────
Γ ⊢ e₁ e₂ ⇒ B
```

### Key Papers

- Pierce & Turner (1998): "Local Type Inference" - the foundational paper
- Dunfield & Krishnaswami (2021): ["Bidirectional Typing"](https://arxiv.org/abs/1908.05839) - comprehensive survey
- Dunfield & Krishnaswami: ["Complete and Easy Bidirectional Typechecking for Higher-Rank Polymorphism"](https://www.cl.cam.ac.uk/~nk480/bidir.pdf)

---

## Part 5: Constraint-Based Type Inference

### Approach

Instead of interleaving constraint generation and solving:
1. **Generate constraints** from AST
2. **Solve constraints** via unification

```
Γ ⊢c e : τ | C
```
"Under Γ, expression e has type τ given constraints C"

### HM(X) Framework

Parameterizes HM over constraint domain X:
- **HM(=)**: Standard HM with equality constraints
- **HM(<:)**: HM with subtyping constraints
- **HM(TC)**: HM with type class constraints

### Benefits

- **Cleaner separation**: Generation vs. solving are independent
- **Better error messages**: Can analyze constraint graph
- **Extensibility**: Add new constraint kinds easily

---

## Part 6: Advanced Topics

### Algebraic Subtyping (MLsub)

Combines subtyping with ML-style parametric polymorphism:

- **Principal types preserved**: Unlike traditional subtyping
- **Compact types**: Uses type simplification exploiting connections to regular language algebra
- **Biunification**: Extended unification handling subtyping constraints

**Simple-sub** (2020): Simplified implementation in ~500 lines with equivalent behavior.

**MLstruct** (2024): Extends to intersection/union/negation types with principal inference.

Key papers:
- [MLsub (POPL 2017)](https://dl.acm.org/doi/10.1145/3009837.3009882)
- [Simple-sub (ICFP 2020)](https://dl.acm.org/doi/10.1145/3409006)

### Row Polymorphism

Enables polymorphism over record/variant fields:

```
{x : int, y : string, ..ρ}  -- record with extra fields ρ
```

**Key concepts:**
- **Rows**: Mappings from labels to types with a "rest" variable
- **Lacks constraints**: Prevent duplicate fields
- **Dual for variants**: Same mechanism works for sum types

**Unification for rows:**
1. Same fields → unify rest types
2. Subset → add missing fields, share rest
3. Different unique fields → create fresh shared rest

Languages using row polymorphism: OCaml (objects, polymorphic variants), PureScript, Koka (effects).

Key paper: [Gaster & Jones: "A Polymorphic Type System for Extensible Records and Variants"](http://web.cecs.pdx.edu/~mpj/pubs/polyrec.html)

### GADTs and OutsideIn(X)

GADTs create challenges for type inference due to local type assumptions.

**OutsideIn(X)** addresses this:
- **Implication constraints**: Layer over base constraint domain
- **Modular solving**: Novel strategy for implication constraints
- **Principal types only**: Accepts only programs with principal types

Key insight: Abandons local let-binding generalization (controversial but practical).

Implemented in GHC 7+.

Paper: [OutsideIn(X)](https://www.microsoft.com/en-us/research/publication/outsideinx-modular-type-inference-with-local-assumptions/)

### Higher-Rank Polymorphism

Types with nested ∀ quantifiers:
```
(∀α. α → α) → (Int, Bool)  -- rank-2 type
```

**Challenges:**
- Full inference is undecidable
- Requires annotations at higher-rank positions

**Solutions:**
- Bidirectional checking with subsumption
- [Practical Type Inference for Arbitrary-Rank Types](https://www.cambridge.org/core/journals/journal-of-functional-programming/article/practical-type-inference-for-arbitraryrank-types/5339FB9DAB968768874D4C20FA6F8CB6)

---

## Part 7: Elaboration in Dependent Types

### Overview

Elaboration: converting partially-specified expressions to fully type-correct terms.

### Lean's Elaborator

Key features:
- **Higher-order unification**: Handles metavariables in higher-order positions
- **Type class inference**: Resolves implicit instances
- **Coercion insertion**: Automatically converts between types
- **Tactic integration**: Mixes proof tactics with elaboration

### Metavariables

Placeholders for unknown terms/types:
```lean
?m : ?A  -- metavariable m of unknown type A
```

Solved by unification during elaboration.

### Key Resources

- [Elaboration in Dependent Type Theory (Lean)](https://leodemoura.github.io/files/elaboration.pdf)
- [Adam Gundry's Thesis](https://adam.gundry.co.uk/pub/thesis/)
- [Richard Eisenberg's Thesis (Dependent Haskell)](https://www.cis.upenn.edu/~sweirich/papers/eisenberg-thesis.pdf)

---

## Part 8: Practical Implementation

### Implementation Strategies

1. **Substitution-based (Algorithm W style)**
   - Thread substitutions through recursion
   - Pure functional, easy to test
   - Less efficient due to repeated application

2. **Union-find based (Algorithm J style)**
   - Mutable references for type variables
   - Efficient equivalence class merging
   - More complex to implement correctly

3. **Constraint generation + solving**
   - Separate phases for clarity
   - Better for error messages
   - Natural for extensions (subtyping, etc.)

### Error Messages

Good error messages require:
- **Source locations**: Track spans through inference
- **Type variable naming**: Rename `'t123` to `'a` for readability
- **Context**: Show what was being typed when error occurred
- **Algorithm M**: Catches errors earlier with more context

### Testing Type Inference

- **Property-based testing**: Generate random expressions, verify principal types
- **Golden tests**: Known expressions with expected types
- **Coverage**: Include let-polymorphism, occurs check failures, infinite types

### Implementation Resources

- [Write You a Haskell (Stephen Diehl)](http://dev.stephendiehl.com/fun/006_hindley_milner.html)
- [OCaml Type Inference (CS3110)](https://cs3110.github.io/textbook/chapters/interp/inference.html)
- [prakhar1989/type-inference](https://github.com/prakhar1989/type-inference) - OCaml implementation
- [Rust Compiler Type Inference Guide](https://rustc-dev-guide.rust-lang.org/type-inference.html)

---

## Summary: Key Takeaways

1. **HM is the foundation**: Most type inference builds on Hindley-Milner
2. **Let-polymorphism is the key restriction**: Enables decidability
3. **Unification is central**: Robinson's algorithm with occurs check
4. **Bidirectional typing extends reach**: Handles undecidable features with minimal annotations
5. **Modern systems combine approaches**: Constraint-based + bidirectional + specialized solvers
6. **Trade-offs exist**: Full inference vs. expressiveness vs. error quality

## Sources

### Core Papers
- [Hindley-Milner Wikipedia](https://en.wikipedia.org/wiki/Hindley–Milner_type_system)
- [Dunfield & Krishnaswami - Bidirectional Typing (arXiv)](https://arxiv.org/abs/1908.05839)
- [OutsideIn(X) - Microsoft Research](https://www.microsoft.com/en-us/research/publication/outsideinx-modular-type-inference-with-local-assumptions/)

### Tutorials & Implementations
- [Max Bernstein - Damas-Hindley-Milner Two Ways](https://bernsteinbear.com/blog/type-inference/)
- [Max Bernstein - Row Polymorphism](https://bernsteinbear.com/blog/row-poly/)
- [Write You a Haskell](http://dev.stephendiehl.com/fun/006_hindley_milner.html)
- [OCaml Programming Textbook](https://cs3110.github.io/textbook/chapters/interp/inference.html)
- [Cornell Type Inference Lecture](https://www.cs.cornell.edu/courses/cs3110/2011sp/Lectures/lec26-type-inference/type-inference.htm)

### Advanced Topics
- [Simple-sub / Algebraic Subtyping](https://lptk.github.io/programming/2020/03/26/demystifying-mlsub.html)
- [Gaster & Jones - Extensible Records](http://web.cecs.pdx.edu/~mpj/pubs/polyrec.html)
- [Cambridge Row Polymorphism Notes](https://www.cl.cam.ac.uk/teaching/1415/L28/rows.pdf)

### Theses
- [Adam Gundry - Type Inference, Haskell and Dependent Types](https://adam.gundry.co.uk/pub/thesis/)
- [Richard Eisenberg - Dependent Types in Haskell](https://www.cis.upenn.edu/~sweirich/papers/eisenberg-thesis.pdf)
