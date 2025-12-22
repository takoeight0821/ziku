# Grokking the Sequent Calculus (Functional Pearl)

## Metadata

- **Authors**: David Binder, Marco Tzschentke, Marius Müller, Klaus Ostermann
- **Affiliation**: University of Tübingen, Germany
- **Published**: ICFP 2024, Proc. ACM Program. Lang. 8, ICFP, Article 250 (August 2024), 31 pages
- **Links**:
  - [arXiv](https://arxiv.org/abs/2406.14719)
  - [ACM DL](https://dl.acm.org/doi/10.1145/3674639)
  - [PDF](https://ps.informatik.uni-tuebingen.de/publications/binder24grokking.pdf)
  - [GitHub](https://github.com/grokking-sc/grokking-sc)
  - [Interactive Demo](https://grokking-sc.github.io/grokking-sc/)

## Abstract

The sequent calculus is a proof system which was designed as a more symmetric alternative to natural deduction. The λμμ̃-calculus is a term assignment system for the sequent calculus and a great foundation for compiler intermediate languages due to its first-class representation of evaluation contexts. Unfortunately, only experts of the sequent calculus can appreciate its beauty. To remedy this, the authors present the first introduction to the λμμ̃-calculus which is not directed at type theorists or logicians but at compiler hackers and programming-language enthusiasts. They do this by writing a compiler from a small but interesting surface language to the λμμ̃-calculus as a compiler intermediate language.

## Problem Statement

The λμμ̃-calculus is a powerful foundation for compiler intermediate languages, but it has been inaccessible to most compiler writers and programming language enthusiasts because:

1. Most existing introductions presuppose knowledge of the sequent calculus
2. The theoretical presentations spend significant space on logical foundations before getting to programming applications
3. There was no practical, implementation-focused introduction available

The authors argue that just as one can understand the lambda calculus without first learning about natural deduction proofs, one should also be able to understand the λμμ̃-calculus without knowing the sequent calculus.

## Key Contributions

1. **First practical introduction** to the λμμ̃-calculus for compiler implementors
2. **Complete compiler implementation** from a surface language (Fun) to a sequent-calculus-based intermediate language (Core)
3. **Clear explanation** of producers, consumers, and statements as the three syntactic categories
4. **Demonstration** of key programming language concepts through the lens of sequent calculus:
   - Duality between data and codata types
   - Duality between let-bindings and control operators
   - Case-of-case transformation as μ-reduction
   - First-class evaluation contexts

## Core Concepts

### Three Syntactic Categories

The λμμ̃-calculus distinguishes three syntactic categories:

| Category | Description | Corresponds to |
|----------|-------------|----------------|
| **Producers** | Construct/produce elements of a type | Introduction forms, proof terms |
| **Consumers** | Consume/destruct elements of a type | Evaluation contexts, continuations |
| **Statements** | Drive computation, no return type | Redexes, IO actions |

### Key Constructs

```
Producers:  p ::= x | ⌜n⌝ | μα.s | K(p̄; c̄) | cocase {D(x̄; ᾱ) ⇒ s}
Consumers:  c ::= α | μ̃x.s | case {K(x̄; ᾱ) ⇒ s} | D(p̄; c̄)
Statements: s ::= ⟨p | c⟩ | ⊙(p₁, p₂; c) | ifz(p, s₁, s₂) | f(p̄; c̄)
```

- **μα.s** (mu-abstraction): Turns a statement into a producer, binding covariable α
- **μ̃x.s** (mu-tilde): Turns a statement into a consumer, binding variable x
- **⟨p | c⟩** (cut): Combines a producer and consumer of the same type

### Evaluation Rules

```
⟨μα.s | c̄⟩  ⊲  s[c̄/α]     -- μ-reduction
⟨p̄ | μ̃x.s⟩  ⊲  s[p̄/x]     -- μ̃-reduction (for values p̄)
⊙(⌜n⌝, ⌜m⌝; c)  ⊲  ⟨⌜n ⊙ m⌝ | c⟩
```

### Critical Pairs and Evaluation Order

A statement of the form `⟨μα.s₁ | μ̃x.s₂⟩` is a **critical pair** that can reduce in two ways:
- **Call-by-value**: Reduce μ first → `s₁[μ̃x.s₂/α]`
- **Call-by-name**: Reduce μ̃ first → `s₂[μα.s₁/x]`

The paper uses call-by-value, where only values can be substituted for variables.

## Translation from Fun to Core

The paper defines a translation `⟦−⟧` from the surface language Fun to Core:

| Fun | Core |
|-----|------|
| `x` | `x` |
| `⌜n⌝` | `⌜n⌝` |
| `t₁ ⊙ t₂` | `μα. ⊙(⟦t₁⟧, ⟦t₂⟧; α)` |
| `ifz(t₁, t₂, t₃)` | `μα.ifz(⟦t₁⟧, ⟨⟦t₂⟧ \| α⟩, ⟨⟦t₃⟧ \| α⟩)` |
| `let x = t₁ in t₂` | `μα.⟨⟦t₁⟧ \| μ̃x.⟨⟦t₂⟧ \| α⟩⟩` |
| `λx.t` | `cocase {ap(x; α) ⇒ ⟨⟦t⟧ \| α⟩}` |
| `t₁ t₂` | `μα.⟨⟦t₁⟧ \| ap(⟦t₂⟧; α)⟩` |
| `label α {t}` | `μα.⟨⟦t⟧ \| α⟩` |
| `goto(t; α)` | `μβ.⟨⟦t⟧ \| α⟩` |

## Focusing

**Static focusing** is a transformation that ensures all subexpressions are in a form where they can be evaluated. It lifts non-value subexpressions to the outside using μ̃-bindings:

```
F(⊙(p₁, p₂, c)) = ⟨F(p₁) | μ̃x.F(⊙(x, p₂, c))⟩  (p₁ not a value)
```

This is similar to A-normal form (ANF) transformation but with explicit continuation handling.

## Key Insights

### 1. Evaluation Contexts are First-Class

In the λμμ̃-calculus, evaluation contexts like `□ * 5` can be bound to covariables and manipulated as first-class values. This is represented as `μ̃x. *(x, ⌜5⌝; α)`.

### 2. Data is Dual to Codata

Data types and codata types are perfectly symmetric in Core:
- **Data types**: Defined by constructors, consumed by case expressions
- **Codata types**: Defined by destructors, produced by cocase expressions

### 3. Let-Bindings are Dual to Control Operators

| Construct | Translation | Binds |
|-----------|-------------|-------|
| `let x = t₁ in t₂` | μ̃-binding | Variable x |
| `label α {t}` | μ-binding | Covariable α |

### 4. Case-of-Case is μ-Reduction

The case-of-case transformation:
```
case (case e₁ of {T ⇒ e₂; F ⇒ e₃}) of {T ⇒ e₄; F ⇒ e₅}
```
becomes:
```
case e₁ of {T ⇒ case e₂ of {...}; F ⇒ case e₃ of {...}}
```

In the λμμ̃-calculus, this is simply a μ-reduction - no special compiler pass needed!

### 5. η-Laws Depend on Evaluation Order

- **Call-by-value**: η-laws for data types are valid
- **Call-by-name**: η-laws for codata types are valid

### 6. Linear Logic Dualities

The paper shows how different types correspond to linear logic connectives:

| Type | Linear Logic | Usage |
|------|-------------|-------|
| Pair(σ, τ) | σ ⊗ τ (tensor) | Must use both components |
| LPair(σ, τ) | σ & τ (with) | Choose one component |
| σ ⊕ τ (Either) | Plus | Tagged union, caller checks |
| σ ⅋ τ (Par) | Par | Two continuations, callee decides |

## Implementation

### Project Structure

```
src/
├── Compiler.hs        # Fun → Core translation
├── Fun/
│   ├── Syntax.hs      # Surface language AST
│   ├── Parser.hs      # Parser
│   └── Types.hs       # Type definitions
└── Core/
    ├── Syntax.hs      # Core language AST
    ├── Eval.hs        # Evaluator
    ├── Focusing.hs    # Static focusing transformation
    ├── Substitution.hs # Capture-avoiding substitution
    └── Simplify.hs    # Administrative redex simplification
```

### Core Syntax (Haskell)

```haskell
data Producer
    = Var Var
    | Lit Int
    | Mu Covar Statement
    | Constructor Ctor [Producer] [Consumer]
    | Cocase [Pattern Dtor]

data Consumer
    = Covar Covar
    | MuTilde Var Statement
    | Case [Pattern Ctor]
    | Destructor Dtor [Producer] [Consumer]

data Statement
    = Cut Producer Consumer
    | Op Producer BinOp Producer Consumer
    | IfZ Producer Statement Statement
    | Fun Name [Producer] [Consumer]
```

### Example: Fast Multiplication

Surface language (Fun):
```
def mult(l) := label α { mult'(l; α) }
def mult'(l; α) := case l of {
    Nil => 1,
    Cons(x, xs) => ifz(x, goto(0; α), x * mult'(xs; α))
}
```

Compiled to Core:
```
def mult(l; α) := mult'(l; α, α)
def mult'(l; α, β) :=
    ⟨l | case {
        Nil ⇒ ⟨1 | β⟩,
        Cons(x, xs) ⇒ ifz(x, ⟨0 | α⟩, mult'(xs; α, μ̃z. *(x, z; β)))
    }⟩
```

## Related Work

### Foundational Papers

1. **Curien & Herbelin (2000)**: "The Duality of Computation" - Original λμμ̃-calculus paper
2. **Gentzen (1935)**: Original sequent calculus papers
3. **Downen et al. (2016)**: ["Sequent Calculus as a Compiler Intermediate Language"](https://www.microsoft.com/en-us/research/publication/sequent-calculus-as-a-compiler-intermediate-language/) - GHC Sequent Core

### Other Related Work by Authors

- **Ostermann et al. (2022)**: "Introduction and Elimination, Left and Right" (ICFP)
- **Binder et al. (2022)**: "Administrative Normal Forms and Focusing for Lambda Calculi"
- **Binder et al. (2025)**: "Compiling Classical Sequent Calculus to Stock Hardware"

### Further Reading

- **Wadler (2003, 2005)**: Call-by-value is dual to call-by-name
- **Downen & Ariola (2018)**: Tutorial on computational classical logic
- **Abel et al. (2013)**: Copatterns
- **Downen et al. (2019)**: Codata in Action

## Limitations & Future Work

1. **Type Inference**: The paper uses Hindley-Milner without let-generalization
2. **Polymorphism**: Not covered in detail
3. **Polarity**: Mixed evaluation orders (call-by-push-value style) not explored
4. **Code Generation**: Translation to machine code not addressed

## Personal Notes

This paper is excellent for understanding why the sequent calculus matters for practical compiler construction. Key takeaways:

1. **Evaluation contexts as first-class citizens** - The μ̃ construct makes continuations explicit without the type complexity of CPS
2. **Symmetry clarifies design** - Data/codata duality helps understand language features
3. **Optimizations for free** - Case-of-case and other transformations are just reductions
4. **Direct vs indirect consumers** - Sequent calculus preserves structure that CPS loses

The interactive web demo is particularly useful for understanding how the compilation and evaluation work.

## Sources

- [arXiv Preprint](https://arxiv.org/abs/2406.14719)
- [ACM Digital Library](https://dl.acm.org/doi/10.1145/3674639)
- [PDF from University of Tübingen](https://ps.informatik.uni-tuebingen.de/publications/binder24grokking.pdf)
- [GitHub Repository](https://github.com/grokking-sc/grokking-sc)
- [Interactive Web Demo](https://grokking-sc.github.io/grokking-sc/)
- [David Binder's Publications](https://binderdavid.github.io/publications/)
- [Sequent Calculus as a Compiler IL (ICFP 2016)](https://www.microsoft.com/en-us/research/publication/sequent-calculus-as-a-compiler-intermediate-language/)
- [Simon Peyton Jones on Sequent Calculus](https://simon.peytonjones.org/sequent-calculus/)
