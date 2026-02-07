# Rank-n Polymorphism in HM Type Systems: Solutions for Ziku

## Date: 2026-02-06

## Problem Statement

Ziku's type system has two interrelated issues:

1. **`let` does not generalize**: Constraint-based HM collects all constraints and solves them at the end, making intermediate generalization at `let` boundaries impossible. Currently, only explicitly annotated `let` bindings (with `forall`) are polymorphic.

2. **Records with polymorphic fields**: The signature type `{ id : forall a. a -> a }` places `forall` inside a record — a Rank-n type. HM cannot represent this. The current `instantiateTy` workaround strips all `forall`s eagerly (including inner ones), but this only works for imports and creates an asymmetry with regular `let` bindings.

These problems manifest concretely:

```
-- FAILS: let without annotation is monomorphic
let id = \x => x in (id 42, id true)

-- WORKS: explicit forall annotation (prenex)
let id : forall a. a -> a = \x => x in (id 42, id true)

-- FAILS: forall inside record (Rank-2)
let r : { id : forall a. a -> a } = { id = \x => x } in (r.id 42, r.id true)

-- WORKS: forall outside record (prenex, Rank-1)
let r : forall a. { id : a -> a } = { id = \x => x } in (r.id 42, r.id true)
```

## Approach Comparison Matrix

| Approach | Let-gen | Rank-n records | Annotation burden | Implementation complexity | Decidable |
|----------|---------|----------------|-------------------|--------------------------|-----------|
| Level-based HM | Yes | No | None | Low-Medium | Yes |
| Bidirectional (Dunfield-Krishnaswami) | Yes | Rank-2+ | At higher-rank args | Medium | Yes |
| HMF (Leijen) | Yes | Yes | Polymorphic args | Medium | Yes |
| FreezeML (Emrich et al.) | Yes | Yes (with freeze) | Minimal (freeze annotation) | Medium | Yes |
| Quick Look (Serrano et al.) | Yes | Yes (partial) | At ambiguous sites | Medium | Yes |
| 1ML (Rossberg) | Yes | Yes | wrap/unwrap for large types | High | Yes |
| OCaml-style explicit poly | Yes | Rank-2 records | Record type declarations | Low | Yes |
| Drop let-gen (Vytiniotis et al.) | No (explicit) | Depends on extension | More annotations | Low (simplifies) | Yes |

---

## 1. Level-Based Let-Generalization

### Key Paper
- **"Efficient and Insightful Generalization"** — Oleg Kiselyov (2013, updated 2022)
  - [https://okmij.org/ftp/ML/generalization.html](https://okmij.org/ftp/ML/generalization.html)
- **"Practical Type Inference with Levels"** — Fan, Xu, Xie (PLDI 2025, Distinguished Paper)
  - [https://dl.acm.org/doi/10.1145/3729338](https://dl.acm.org/doi/10.1145/3729338)

### Core Idea

Assign each type variable a **level** (integer) representing the nesting depth of the `let` expression that created it. Generalization becomes trivial: quantify all variables whose level exceeds the current level.

```
level 0:  (top-level)
level 1:  let x = ...    ← fresh vars get level 1
level 0:  in ...          ← generalize vars with level > 0
```

### Algorithm

1. Maintain a global `current_level` counter
2. Before typing `let`-bound expression: `current_level += 1`
3. Fresh type variables are created at `current_level`
4. After typing: `current_level -= 1`
5. **Generalize**: all free type variables with level > `current_level` become quantified
6. During **unification**: when unifying `?a` (level 3) with a type containing `?b` (level 1), update `?a`'s level to `min(3, 1) = 1` — the variable "escapes" to the outer scope

### Relationship to Constraint Solving

The key insight is that levels can be integrated into constraint-based inference. Instead of solving all constraints at the end, levels allow **deferred generalization**: constraints are still collected globally, but the level annotations on type variables provide enough information to determine which variables can be generalized at which `let` boundary during the final solve phase.

### Applicability to Ziku

**Solves**: Problem 1 (let-generalization).
**Does not solve**: Problem 2 (Rank-n records). Levels alone only give standard HM let-polymorphism — `forall` is still prenex only.

**Implementation effort**: Low-Medium. Requires:
- Adding a `level : Nat` field to type variables
- Modifying `freshTyVar` to use current level
- Modifying `unifyAt` to propagate minimum levels
- Adding generalization logic at `let` boundaries in `genConstraints`

---

## 2. Bidirectional Type Checking for Higher-Rank Types

### Key Papers
- **"Complete and Easy Bidirectional Typechecking for Higher-Rank Polymorphism"** — Dunfield & Krishnaswami (ICFP 2013)
  - [https://arxiv.org/abs/1306.6032](https://arxiv.org/abs/1306.6032)
- **"Practical Type Inference for Arbitrary-Rank Types"** — Peyton Jones, Vytiniotis, Weirich, Shields (JFP 2007)
  - [https://www.cambridge.org/core/journals/journal-of-functional-programming/article/practical-type-inference-for-arbitraryrank-types/5339FB9DAB968768874D4C20FA6F8CB6](https://www.cambridge.org/core/journals/journal-of-functional-programming/article/practical-type-inference-for-arbitraryrank-types/5339FB9DAB968768874D4C20FA6F8CB6)

### Core Idea

Split type inference into two modes:

- **Synthesis (⇒)**: The term generates its type (bottom-up)
- **Checking (⇐)**: The term is checked against a known type (top-down)

Higher-rank types flow through checking mode. When a function argument has a known polymorphic type, the argument is **checked** against that type rather than synthesized.

### Key Rules

```
Γ ⊢ e ⇐ ∀a. A        -- checking against a polytype
────────────────────   -- introduce a fresh "rigid" variable â
Γ ⊢ e ⇐ [â/a]A       -- check body with â

Γ ⊢ f ⇒ ∀a. A → B    -- function synthesizes a polytype
Γ ⊢ arg ⇐ [â/a]A     -- check argument against instantiated domain
────────────────────
Γ ⊢ f arg ⇒ [â/a]B
```

### Annotation Requirements

- **Rank-1**: No annotations needed (same as HM)
- **Rank-2+**: Annotations needed where polymorphic values are passed as arguments
- **Practical**: Only the "outermost" annotation matters; inner types are propagated

Example:
```
-- Annotation needed: f takes a polymorphic argument
let apply (f : forall a. a -> a) = (f 42, f true)
```

### Applicability to Ziku

**Solves**: Both problems. Let-generalization works via synthesis mode; record field access in checking mode can propagate `forall` types.

**Implementation effort**: Medium-High. Requires restructuring inference from pure constraint-generation to a bidirectional algorithm. Significant refactor of `Infer.lean`.

---

## 3. HMF: Simple Type Inference for First-Class Polymorphism

### Key Paper
- **"HMF: Simple Type Inference for First-Class Polymorphism"** — Daan Leijen (ICFP 2008)
  - [https://www.microsoft.com/en-us/research/publication/hmf-simple-type-inference-for-first-class-polymorphism/](https://www.microsoft.com/en-us/research/publication/hmf-simple-type-inference-for-first-class-polymorphism/)
  - Reference implementation: [https://github.com/sinelaw/hmf](https://github.com/sinelaw/hmf)

### Core Idea

HMF extends Algorithm W with a **subsumption** relation that allows polymorphic types to be used where monomorphic types are expected, and vice versa (with annotations). The key innovation is using **flexible** and **rigid** type variables:

- **Flexible** variables (from inference): can be unified with polytypes
- **Rigid** variables (from annotations): must be matched exactly

### Annotation Rules

1. Polymorphic **function parameters** must be annotated
2. Ambiguous impredicative **instantiations** must be annotated
3. Everything else is inferred

```
-- Annotation needed: polymorphic parameter
let apply (f : forall a. a -> a) = (f 42, f true)

-- No annotation needed: let-bound values
let id = \x => x in (id 42, id true)

-- Records with polymorphic fields: annotation on the record type
let r : { id : forall a. a -> a } = { id = \x => x }
r.id 42    -- OK
r.id true  -- OK
```

### Key Technical Detail: Subsumption

HMF defines `σ ≤ σ'` (σ is more polymorphic than σ'):
```
∀a. a → a  ≤  Int → Int        (instantiation)
Int → Int  ≤  ∀a. a → a        (FAILS: not more general)
```

This replaces standard unification at application sites, allowing polymorphic types to flow through the system.

### Applicability to Ziku

**Solves**: Both problems elegantly. Records with polymorphic fields work naturally because field types carry `forall`.

**Implementation effort**: Medium. Extends the existing Algorithm W-style inference with subsumption. Does not require full restructuring to bidirectional — it's a "small extension of Algorithm W."

---

## 4. FreezeML

### Key Paper
- **"FreezeML: Complete and Easy Type Inference for First-Class Polymorphism"** — Emrich, Lindley, Stolarek, Cheney, Coates (PLDI 2020)
  - [https://arxiv.org/abs/2004.00396](https://arxiv.org/abs/2004.00396)

### Core Idea

FreezeML adds a single syntactic annotation: the **freeze** operator (`$`), which prevents a variable from being instantiated. This allows programmers to explicitly control where polymorphism is preserved.

```
let id = \x => x        -- id : forall a. a -> a (generalized)
id 42                    -- id is instantiated to Int -> Int
$id                      -- id keeps its polymorphic type (frozen)
let f = \g => (g 42, g true) in f $id   -- works!
```

### Key Properties

- **Conservative extension of ML**: All ML programs are valid FreezeML programs
- **Sound and complete**: Type inference yields principal types
- **Minimal annotation**: Only `$` at variable use sites where polymorphism must be preserved
- **System F equivalence**: Type-preserving translations to and from System F

### How It Handles Records

```
let r = { id = \x => x }    -- r : forall a. { id : a -> a }
r.id 42                      -- r instantiated, id : Int -> Int
($r).id 42                   -- r frozen, but still need to access field...
```

FreezeML's approach to records is less natural because freeze operates on variable references, not on individual record fields. For per-field polymorphism, you'd need the record type itself to express it.

### Applicability to Ziku

**Solves**: Problem 1 (let-generalization). Partially addresses Problem 2 (records) — frozen variables preserve their full polymorphic type, but per-field polymorphism in records requires additional design.

**Implementation effort**: Medium. Extends Algorithm W. The constraint-based version of FreezeML is described in a follow-up paper (Emrich & Lindley, ICFP 2022).

---

## 5. Quick Look Impredicativity

### Key Paper
- **"A Quick Look at Impredicativity"** — Serrano, Hage, Peyton Jones, Vytiniotis (ICFP 2020)
  - [https://dl.acm.org/doi/10.1145/3408971](https://dl.acm.org/doi/10.1145/3408971)

### Core Idea

Quick Look adds a **pre-pass** ("quick look") over function arguments before full type inference. This pre-pass quickly determines whether arguments should be given polymorphic types, guiding the main inference.

### Two-Pass Algorithm

1. **Quick Look pass**: Scan arguments to determine instantiation decisions. If an argument is a variable with a known polymorphic type, or a lambda with a type annotation, record this.
2. **Main inference**: Use the information from the quick look to make informed instantiation decisions.

### Key Properties

- Implemented in **GHC** (production quality)
- Only changes the `APP` rule — minimal invasion
- 1% of GHC's inference engine was affected
- Compatible with all other GHC type system extensions

### Applicability to Ziku

**Partially solves**: Both problems. Quick Look can detect when data constructors (including record constructors) need impredicative instantiation. However, it's designed for Haskell's type system which already has let-generalization.

**Implementation effort**: Medium. Requires a pre-pass but otherwise integrates into existing inference.

---

## 6. OCaml-Style Explicit Polymorphic Record Fields

### Reference
- [OCaml Manual: Polymorphism and its Limitations](https://ocaml.org/manual/5.4/polymorphism.html)
- [OCaml Discuss: Polymorphic Record Fields](https://discuss.ocaml.org/t/any-way-to-define-a-polymorphic-record-field-via-a-function/1916)

### Core Idea

OCaml allows **explicit universal quantification** in record field type declarations:

```ocaml
type 'a nested = List of 'a list | Nested of 'a list nested

(* Record with explicitly polymorphic field *)
type nested_reduction = { f : 'a. 'a nested -> int }

let boxed_len = { f = List.length }   (* f is polymorphic *)
let _ = boxed_len.f (List [1;2;3])    (* f : int list nested -> int *)
let _ = boxed_len.f (List ["a";"b"])   (* f : string list nested -> int *)
```

### How It Works

1. Record **type declarations** must explicitly quantify field-level `forall`
2. The type checker treats these fields as having a **scheme** (not a monotype)
3. Each field **access** instantiates the scheme with fresh variables
4. Record **construction** checks that the provided value is at least as polymorphic as the declared scheme

### Limitations

- Requires **nominal record types** (must declare the type first)
- Cannot construct a polymorphic record field from a monomorphic function — the function must already be polymorphic
- Only works for record fields and object methods, not arbitrary expressions

### Applicability to Ziku

**Partially solves**: Problem 2 (records with polymorphic fields), but requires nominal record types rather than Ziku's structural records with row polymorphism.

**Could be adapted**: Ziku's `.ziki` signature files could serve as the "type declaration" that specifies per-field quantification. The import system already does something similar with `instantiateTy`.

**Implementation effort**: Low-Medium. Requires:
- A way to specify per-field quantification (signatures already do this)
- Treating record field types as schemes during field access
- Checking polymorphism during record construction

---

## 7. 1ML: Core and Modules United

### Key Paper
- **"1ML — Core and Modules United"** — Andreas Rossberg (JFP 2018)
  - [https://people.mpi-sws.org/~rossberg/papers/Rossberg%20-%201ML%20--%20Core%20and%20modules%20united%20%5BJFP%5D.pdf](https://people.mpi-sws.org/~rossberg/papers/Rossberg%20-%201ML%20--%20Core%20and%20modules%20united%20%5BJFP%5D.pdf)
  - Prototype: [https://github.com/rossberg/1ml](https://github.com/rossberg/1ml)

### Core Idea

1ML eliminates the distinction between core and module language. Every expression is a "module." Records and structures are unified. Polymorphism is controlled by a **small/large type** distinction:

- **Small types**: Monomorphic types, type variables, simple functions (decidable inference)
- **Large types**: Types containing abstract types or polymorphism (require annotations)

Impredicativity is available but requires explicit `wrap`/`unwrap` operations to cross the small/large boundary.

### Applicability to Ziku

**Solves**: Both problems in principle. The module = record design aligns with Ziku's import system.

**Implementation effort**: High. Requires F-omega as the internal language and a fundamentally different type system architecture.

---

## 8. "Let Should Not Be Generalised"

### Key Paper
- **"Let Should Not Be Generalised"** — Vytiniotis, Peyton Jones, Schrijvers, Sulzmann (TLDI 2010)
  - [https://www.microsoft.com/en-us/research/wp-content/uploads/2016/02/tldi10-vytiniotis.pdf](https://www.microsoft.com/en-us/research/wp-content/uploads/2016/02/tldi10-vytiniotis.pdf)

### Core Argument

For type systems more complex than vanilla HM (GADTs, type families, local assumptions), implicit let-generalization creates **disproportionate complexity** and is **seldom used** in practice. The authors propose requiring explicit annotations for polymorphic `let` bindings.

### Relevance to Ziku

Ziku **already** follows this approach (whether by design or accident): `let` without annotation is monomorphic, and `let` with `forall` annotation is polymorphic. This simplifies the type system significantly.

The question is whether this tradeoff is acceptable for Ziku's goals.

---

## Recommended Strategy for Ziku

### Phase 1: Level-Based Let-Generalization (Short-term)

**Goal**: Make `let id = \x => x in (id 42, id true)` work without annotations.

**Why**: This is the most impactful improvement with the lowest implementation cost. It fixes the most common annoyance (needing `forall` annotations for simple polymorphic bindings) without requiring any new syntax or type system concepts.

**Implementation sketch**:
1. Add `level : Nat` field to type variable representation
2. Track `currentLevel : Nat` in `GenState`
3. In `genConstraints` for `.let_`: increment level before `e1`, decrement after
4. In `freshTyVar`: assign `currentLevel` to new variables
5. In `unifyAt`: propagate minimum level during variable unification
6. After solving constraints: generalize variables whose level exceeds the binding level

**Key reference**: Kiselyov's [Efficient and Insightful Generalization](https://okmij.org/ftp/ML/generalization.html) — contains a complete, readable implementation.

### Phase 2: OCaml-Style Polymorphic Record Fields (Medium-term)

**Goal**: Make `{ id : forall a. a -> a }` work correctly in record types.

**Why**: This directly addresses the import signature problem and enables per-field polymorphism. It aligns with how `.ziki` signatures already work.

**Implementation sketch**:
1. During field access (`.field`): if the field type contains `forall`, treat it as a scheme and instantiate
2. During record construction: if the expected field type is `forall a. T`, check that the provided value can be generalized to that type
3. The existing `instantiateTy` logic (used for imports) already does most of this — extend it to work uniformly for all records, not just imports

**Key reference**: [OCaml Manual: Polymorphism](https://ocaml.org/manual/5.4/polymorphism.html) — Section on universally quantified record fields.

### Phase 3: Bidirectional Type Checking (Long-term, optional)

**Goal**: Full higher-rank polymorphism with minimal annotations.

**Why**: Enables passing polymorphic values as function arguments, which is needed for advanced module patterns.

**Key reference**: Dunfield & Krishnaswami's [Complete and Easy Bidirectional Typechecking](https://arxiv.org/abs/1306.6032) — the simplest and most well-understood approach.

---

## Alternative: Accept Current Design

Ziku's current approach (explicit `forall` annotations for polymorphism) is a valid design point, aligned with the argument in "Let Should Not Be Generalised." Many modern type systems are moving toward more explicit polymorphism (e.g., Haskell's `TypeApplications`, Rust's turbofish). The question is whether the annotation burden is acceptable for Ziku's target use cases.

---

## Sources

### Papers
- [Let Should Not Be Generalised](https://www.microsoft.com/en-us/research/wp-content/uploads/2016/02/tldi10-vytiniotis.pdf) — Vytiniotis et al., TLDI 2010
- [Complete and Easy Bidirectional Typechecking for Higher-Rank Polymorphism](https://arxiv.org/abs/1306.6032) — Dunfield & Krishnaswami, ICFP 2013
- [Practical Type Inference for Arbitrary-Rank Types](https://www.cambridge.org/core/journals/journal-of-functional-programming/article/practical-type-inference-for-arbitraryrank-types/5339FB9DAB968768874D4C20FA6F8CB6) — Peyton Jones et al., JFP 2007
- [HMF: Simple Type Inference for First-Class Polymorphism](https://www.microsoft.com/en-us/research/publication/hmf-simple-type-inference-for-first-class-polymorphism/) — Leijen, ICFP 2008
- [FreezeML: Complete and Easy Type Inference for First-Class Polymorphism](https://arxiv.org/abs/2004.00396) — Emrich et al., PLDI 2020
- [A Quick Look at Impredicativity](https://dl.acm.org/doi/10.1145/3408971) — Serrano et al., ICFP 2020
- [MLF: Raising ML to the Power of System F](https://people.cs.nott.ac.uk/pszgmh/appsem-papers/lebotlan.pdf) — Le Botlan & Rémy, ICFP 2003
- [1ML — Core and Modules United](https://people.mpi-sws.org/~rossberg/papers/Rossberg%20-%201ML%20--%20Core%20and%20modules%20united%20%5BJFP%5D.pdf) — Rossberg, JFP 2018
- [OutsideIn(X): Modular Type Inference with Local Assumptions](https://www.cambridge.org/core/journals/journal-of-functional-programming/article/outsideinx-modular-type-inference-with-local-assumptions/65110D74CF75563F91F9C68010604329) — Vytiniotis et al., JFP 2011
- [Practical Type Inference with Levels](https://dl.acm.org/doi/10.1145/3729338) — Fan, Xu, Xie, PLDI 2025 (Distinguished Paper)
- [When Subtyping Constraints Liberate](https://dl.acm.org/doi/10.1145/3632890) — POPL 2024
- [Constraint-based type inference for FreezeML](https://dl.acm.org/doi/10.1145/3547642) — Emrich & Lindley, ICFP 2022

### Implementations
- [HMF Reference Implementation (Haskell)](https://github.com/sinelaw/hmf)
- [1ML Prototype (OCaml)](https://github.com/rossberg/1ml)
- [Bidirectional Typechecking (Haskell)](https://github.com/ollef/Bidirectional)
- [SuperF Artifact](https://github.com/hkust-taco/superf)

### Tutorials and Explanations
- [Efficient and Insightful Generalization](https://okmij.org/ftp/ML/generalization.html) — Oleg Kiselyov
- [OCaml Manual: Polymorphism and its Limitations](https://ocaml.org/manual/5.4/polymorphism.html)
- [Hindley-Milner Inference with Constraints](https://kseo.github.io/posts/2017-01-02-hindley-milner-inference-with-constraints.html) — Kwang Yul Seo
