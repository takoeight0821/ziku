# Type Inference Design for Ziku

## Overview

This document outlines the design of a type inference system for Ziku, a functional programming language with:
- Data types with pattern matching
- Codata types with copattern matching
- Sequent calculus features (`cut`, `mu`)
- Anonymous records
- Polymorphism (Hindley-Milner style with extensions)

## Design Goals

1. **Principal types**: Infer the most general type without annotations
2. **Bidirectional where needed**: Use checking mode for codata/patterns
3. **Row polymorphism**: Flexible records without explicit row variables
4. **Good error messages**: Leverage Algorithm M's early error detection
5. **Codata support**: First-class typing for copatterns and `#`

---

## Part 1: Core Type System

### Type Language

```lean
inductive Ty where
  | var     : Ident → Ty                      -- Type variable: α
  | con     : Ident → Ty                      -- Type constructor: Int, Bool, Stream
  | app     : Ty → Ty → Ty                    -- Type application: List α
  | arrow   : Ty → Ty → Ty                    -- Function type: α → β
  | forall_ : Ident → Ty → Ty                 -- ∀α. τ
  | record  : List (Ident × Ty) → Option Ty → Ty  -- { x : Int, y : Bool | ρ }
```

### Key Design: No Separate Codata Type Constructor

**Codata types are constructed from records and functions**, not as a separate type:

| Codata Block | Inferred Type |
|--------------|---------------|
| `{ #.x => 1, #.y => 2 }` | `{ x : Int, y : Int }` |
| `{ #(x) => x + 1 }` | `Int → Int` |
| `{ #.head => 1, #.tail => s }` | `{ head : Int, tail : Stream Int }` |
| `{ #(x)(y) => x + y }` | `Int → Int → Int` |

This reflects the duality:
- **Data**: Constructed by constructors, destructed by pattern matching
- **Codata**: Constructed by copattern blocks, destructed by field access / application

### Type Schemes

```
σ ::= τ                    -- Monotype
    | ∀α. σ                -- Polytype (quantified at outer level only)
```

### Typing Environment

```lean
structure TyEnv where
  vars      : List (Ident × Scheme)           -- Term variables
  types     : List (Ident × TyDecl)           -- Data/codata type declarations
  codataSig : List (Ident × List CopatSig)    -- Codata signatures for # resolution
```

---

## Part 2: Inference Algorithm

### Choice: Constraint-Based with Bidirectional Checking

We use a **hybrid approach**:
1. **Algorithm J style** for basic expressions (efficient, mutable unification)
2. **Bidirectional checking** for codata blocks and pattern matching
3. **Constraint generation** for complex cases with delayed solving

### Inference Monad

```lean
structure InferState where
  nextVar  : Nat                              -- Fresh variable counter
  subst    : UnionFind Ty                     -- Mutable substitution (union-find)
  errors   : List TypeError                   -- Accumulated errors

abbrev InferM := StateT InferState (ExceptT TypeError IO)
```

### Core Operations

```lean
-- Fresh type variable
def fresh : InferM Ty := do
  let n ← get
  modify fun s => { s with nextVar := s.nextVar + 1 }
  return .var s!"_t{n}"

-- Unification with occurs check
def unify (t1 t2 : Ty) : InferM Unit := do
  let t1' ← zonk t1  -- Apply current substitution
  let t2' ← zonk t2
  unifyZonked t1' t2'

def unifyZonked : Ty → Ty → InferM Unit
  | .var α, t =>
    if occursIn α t then throw (InfiniteType α t)
    else bind α t
  | t, .var α => unifyZonked (.var α) t
  | .con c1, .con c2 =>
    if c1 == c2 then pure () else throw (Mismatch (.con c1) (.con c2))
  | .arrow a1 b1, .arrow a2 b2 => do
    unify a1 a2
    unify b1 b2
  | .app f1 a1, .app f2 a2 => do
    unify f1 f2
    unify a1 a2
  | .record fs1 r1, .record fs2 r2 => unifyRecords fs1 r1 fs2 r2
  | t1, t2 => throw (Mismatch t1 t2)
```

---

## Part 3: Expression Inference

### Bidirectional Judgments

```
Γ ⊢ e ⇒ τ        -- Synthesis: infer type of e
Γ ⊢ e ⇐ τ        -- Checking: check e has type τ
```

### Inference Rules

#### Literals
```
─────────────────────
Γ ⊢ n ⇒ Int

─────────────────────
Γ ⊢ "s" ⇒ String

─────────────────────
Γ ⊢ true ⇒ Bool
```

#### Variables
```
(x : σ) ∈ Γ    τ = inst(σ)
────────────────────────────
Γ ⊢ x ⇒ τ
```

#### Lambda (Synthesis Mode)
```
α, β fresh    Γ, x : α ⊢ e ⇒ τ    unify(τ, β)
───────────────────────────────────────────────
Γ ⊢ λx. e ⇒ α → β
```

#### Lambda (Checking Mode)
```
Γ, x : τ₁ ⊢ e ⇐ τ₂
───────────────────────
Γ ⊢ λx. e ⇐ τ₁ → τ₂
```

#### Application
```
Γ ⊢ e₁ ⇒ τ₁    Γ ⊢ e₂ ⇒ τ₂    α fresh    unify(τ₁, τ₂ → α)
───────────────────────────────────────────────────────────────
Γ ⊢ e₁ e₂ ⇒ α
```

#### Let (with let-polymorphism)
```
Γ ⊢ e₁ ⇒ τ₁    σ = gen(Γ, τ₁)    Γ, x : σ ⊢ e₂ ⇒ τ₂
─────────────────────────────────────────────────────
Γ ⊢ let x = e₁ in e₂ ⇒ τ₂
```

#### Let Rec
```
α fresh    Γ, x : α ⊢ e₁ ⇒ τ₁    unify(α, τ₁)
σ = gen(Γ, zonk(α))    Γ, x : σ ⊢ e₂ ⇒ τ₂
─────────────────────────────────────────────
Γ ⊢ let rec x = e₁ in e₂ ⇒ τ₂
```

#### If-Then-Else
```
Γ ⊢ e₁ ⇐ Bool    Γ ⊢ e₂ ⇒ τ    Γ ⊢ e₃ ⇐ τ
───────────────────────────────────────────
Γ ⊢ if e₁ then e₂ else e₃ ⇒ τ
```

#### Type Annotation
```
Γ ⊢ e ⇐ τ
─────────────────
Γ ⊢ (e : τ) ⇒ τ
```

---

## Part 4: Pattern Matching

### Pattern Type Inference

Patterns both **introduce bindings** and **constrain types**:

```lean
-- Returns: (bindings, pattern type)
def inferPat (env : TyEnv) (p : Pat) : InferM (List (Ident × Ty) × Ty)
```

#### Pattern Rules

```
───────────────────────────────
Γ ⊢ₚ x ⇒ ([(x, α)], α)    -- α fresh

───────────────────────────────
Γ ⊢ₚ _ ⇒ ([], α)          -- α fresh

───────────────────────────────
Γ ⊢ₚ 42 ⇒ ([], Int)

Con : τ₁ → ... → τₙ → T ∈ Γ
Γ ⊢ₚ p₁ ⇒ (Δ₁, τ₁') ... Γ ⊢ₚ pₙ ⇒ (Δₙ, τₙ')
unify(τᵢ, τᵢ') for all i
───────────────────────────────────────────────
Γ ⊢ₚ Con p₁ ... pₙ ⇒ (Δ₁ ∪ ... ∪ Δₙ, T)
```

### Match Expression

```
Γ ⊢ e ⇒ τₛ    for each (pᵢ, eᵢ):
  Γ ⊢ₚ pᵢ ⇒ (Δᵢ, τₚᵢ)    unify(τₛ, τₚᵢ)
  Γ, Δᵢ ⊢ eᵢ ⇒ τᵣᵢ    unify(τᵣ, τᵣᵢ)
──────────────────────────────────────────
Γ ⊢ match e with | p₁ => e₁ | ... end ⇒ τᵣ
```

---

## Part 5: Records with Row Polymorphism

### Record Types

```
τ ::= ... | { l₁ : τ₁, ..., lₙ : τₙ | ρ }
```

Where `ρ` is either:
- `∅` (empty/closed record)
- A row variable `α` (open/extensible record)

### Record Inference

#### Record Literal
```
Γ ⊢ eᵢ ⇒ τᵢ for each field
─────────────────────────────────────────────────
Γ ⊢ { l₁ = e₁, ..., lₙ = eₙ } ⇒ { l₁ : τ₁, ..., lₙ : τₙ | ∅ }
```

#### Field Access
```
Γ ⊢ e ⇒ τ    ρ fresh    unify(τ, { l : α | ρ })
─────────────────────────────────────────────────
Γ ⊢ e.l ⇒ α
```

### Row Unification

```lean
def unifyRecords (fs1 : Fields) (r1 : Option Ty) (fs2 : Fields) (r2 : Option Ty) : InferM Unit := do
  let common := fs1.filter (fun (l, _) => fs2.any (fun (l', _) => l == l'))
  let only1 := fs1.filter (fun (l, _) => !fs2.any (fun (l', _) => l == l'))
  let only2 := fs2.filter (fun (l, _) => !fs1.any (fun (l', _) => l == l'))

  -- Unify common fields
  for (l, t1) in common do
    let t2 := fs2.find! (fun (l', _) => l == l') |>.2
    unify t1 t2

  -- Handle tails
  match r1, r2, only1.isEmpty, only2.isEmpty with
  | none, none, true, true => pure ()
  | some ρ1, none, _, true => unify ρ1 (.record only1 none)
  | none, some ρ2, true, _ => unify ρ2 (.record only2 none)
  | some ρ1, some ρ2, _, _ =>
    let ρ ← fresh
    unify ρ1 (.record only2 (some ρ))
    unify ρ2 (.record only1 (some ρ))
  | _, _, _, _ => throw RecordMismatch
```

---

## Part 6: Codata and Copatterns

### Design Principle: Codata → Record/Function Types

Codata blocks are **syntactic sugar** for constructing values of record or function types.
There is no separate "codata type" - codata is a way of **defining** values, not a type former.

```
Codata declaration:              Equivalent type alias:
─────────────────────────────    ────────────────────────────
codata Stream a {                Stream a = { head : a
  #.head : a                               , tail : Stream a }
  #.tail : Stream a
}

codata a -> b {                  (Already the function type a → b)
  #(a) : b
}
```

### The `#` Symbol

`#` refers to "the object being defined" (self-reference):
- **In copattern position** (LHS): defines behavior when observation is made
- **In expression position** (RHS): recursive reference to the value being constructed

### Codata Block Inference

#### Field Copatterns → Record Type

```ziku
{ #.x => 1, #.y => 2 }
```

**Synthesis rule**:
```
for each clause (#.lᵢ => eᵢ):
  Γ ⊢ eᵢ ⇒ τᵢ
──────────────────────────────────────────────────
Γ ⊢ { #.l₁ => e₁, ..., #.lₙ => eₙ } ⇒ { l₁ : τ₁, ..., lₙ : τₙ }
```

**Checking rule** (with expected type):
```
expected = { l₁ : τ₁, ..., lₙ : τₙ | ρ }
for each clause (#.lᵢ => eᵢ):
  Γ, # : expected ⊢ eᵢ ⇐ τᵢ
──────────────────────────────────────────────────
Γ ⊢ { #.l₁ => e₁, ..., #.lₙ => eₙ } ⇐ expected
```

#### Application Copatterns → Function Type

```ziku
{ #(x) => x + 1 }
```

**Synthesis rule**:
```
α fresh    Γ, x : α ⊢ e ⇒ β
──────────────────────────────
Γ ⊢ { #(x) => e } ⇒ α → β
```

**Checking rule**:
```
Γ, x : τ₁ ⊢ e ⇐ τ₂
──────────────────────────────
Γ ⊢ { #(x) => e } ⇐ τ₁ → τ₂
```

#### Curried Functions

```ziku
{ #(x)(y) => x + y }
-- Equivalent to: { #(x) => { #(y) => x + y } }
```

**Rule**:
```
Γ, x : α ⊢ { #(y) => e } ⇒ β → γ
─────────────────────────────────────
Γ ⊢ { #(x)(y) => e } ⇒ α → β → γ
```

#### Self-Reference with `#`

```ziku
{ #.head => 1, #.tail => # }
```

The `#` on RHS refers to the whole codata block. Type inference:

```
α fresh (representing the result type)
Γ, # : α ⊢ 1 ⇒ Int
Γ, # : α ⊢ # ⇒ α
unify(α, { head : Int, tail : α })
──────────────────────────────────────────────────
Γ ⊢ { #.head => 1, #.tail => # } ⇒ μα. { head : Int, tail : α }
```

Note: This produces a **recursive type**. For named codata like `Stream Int`, we use the declared type name instead of μ.

### Nested Copatterns

```ziku
def fibs : Stream Int = {
  #.head      => 0
  #.tail.head => 1
  #.tail.tail => zipWith (+) fibs fibs.tail
}
```

Nested copatterns like `#.tail.head` are **elaborated** into nested codata blocks:

```ziku
-- Elaborates to:
def fibs : Stream Int = {
  #.head => 0
  #.tail => {
    #.head => 1
    #.tail => zipWith (+) fibs fibs.tail
  }
}
```

**Copattern splitting algorithm**:
1. Group clauses by first accessor
2. For each group, recursively process remaining copattern
3. Build nested codata blocks

```lean
def splitCopatterns (clauses : List (Copattern × Expr)) : Expr :=
  let grouped := clauses.groupBy (·.1.head)
  let fields := grouped.map fun (acc, subclauses) =>
    let subclauses' := subclauses.map fun (cp, e) => (cp.tail, e)
    (acc, if subclauses'.all (·.1.isEmpty)
          then subclauses'.head!.2  -- leaf: just the expression
          else splitCopatterns subclauses')  -- recurse
  Expr.codata fields
```

### Mixed Patterns and Copatterns

```ziku
def map : (a -> b) -> Stream a -> Stream b = {
  f, s #.head => f (s.head)
  f, s #.tail => map f (s.tail)
}
```

**Typing**: Patterns before `#` determine argument types; copattern determines result structure.

```
for each clause (p₁, ..., pₙ #.l => e):
  Γ ⊢ₚ pᵢ ⇒ (Δᵢ, τᵢ)                           -- infer pattern types
  lookup field l in result type → τ_field       -- get field type from result
  Γ, ∪Δᵢ, # : result ⊢ e ⇐ τ_field             -- check body against field type
──────────────────────────────────────────────────────
Γ ⊢ { clauses } ⇒ τ₁ → ... → τₙ → result
```

### Codata Declarations and Type Aliases

```ziku
codata Stream a {
  #.head : a
  #.tail : Stream a
}
```

This declaration:
1. Introduces `Stream` as a **type constructor** (not a separate codata kind)
2. Records the **observation signatures** for type checking codata blocks
3. Equivalent to: `type Stream a = { head : a, tail : Stream a }`

When checking a codata block against `Stream Int`:
- Look up observation signatures: `{ head : Int, tail : Stream Int }`
- Check each clause provides the correct field types

---

## Part 7: Sequent Calculus Features

### Cut Expression

```ziku
cut <producer | consumer>
```

Typing rule:
```
Γ ⊢ producer ⇒ τ    Γ ⊢ consumer ⇐ τ → ⊥
─────────────────────────────────────────
Γ ⊢ cut <producer | consumer> ⇒ ⊥
```

Or with continuation type:
```
Γ ⊢ producer ⇒ τ    Γ ⊢ consumer ⇐ ¬τ
───────────────────────────────────────
Γ ⊢ cut <producer | consumer> ⇒ α
```

Where `¬τ = τ → ⊥` or continuation type.

### Mu Abstraction

```ziku
mu k => e
```

The `μ` binds a **continuation** (consumer):
```
α, β fresh    Γ, k : α → β ⊢ e ⇒ τ    unify(τ, β)
─────────────────────────────────────────────────
Γ ⊢ μk. e ⇒ α
```

---

## Part 8: Generalization and Instantiation

### Generalization

```lean
def generalize (env : TyEnv) (ty : Ty) : Scheme := do
  let ty' ← zonk ty
  let envFVs := env.freeVars
  let tyFVs := ty'.freeVars
  let toQuantify := tyFVs.filter (fun v => !envFVs.contains v)
  Scheme.forall toQuantify ty'
```

### Instantiation

```lean
def instantiate (scheme : Scheme) : InferM Ty := do
  match scheme with
  | .mono ty => return ty
  | .forall vars ty =>
    let freshVars ← vars.mapM (fun _ => fresh)
    let subst := vars.zip freshVars
    return ty.applySubst subst
```

### Value Restriction

For soundness with mutable references (if added later):

```lean
def canGeneralize (e : Expr) : Bool :=
  match e with
  | .lit _ | .var _ | .lam _ _ => true
  | .let_ _ _ e1 e2 => canGeneralize e1 && canGeneralize e2
  | _ => false

def generalizeIf (env : TyEnv) (e : Expr) (ty : Ty) : Scheme :=
  if canGeneralize e then generalize env ty
  else Scheme.mono ty
```

---

## Part 9: Type Declarations

### Data Type Processing

```ziku
data List a =
  | Nil
  | Cons a (List a)
```

Generates:
```
List : Type → Type
Nil  : ∀a. List a
Cons : ∀a. a → List a → List a
```

```lean
def processDataDecl (name : Ident) (params : List Ident) (constrs : List ConDecl) : InferM Unit := do
  -- Register type constructor
  let tyKind := params.foldr (fun _ k => .arrow .type k) .type
  addTypeCon name tyKind

  -- Register constructors
  for con in constrs do
    let conTy := con.args.foldr (fun t acc => .arrow t acc) (mkAppTy name params)
    let scheme := params.foldr (fun p s => .forall_ p s) conTy
    addVar con.name scheme
```

### Codata Type Processing

```ziku
codata Stream a {
  #.head : a
  #.tail : Stream a
}
```

This is equivalent to a **recursive record type alias**:
```
Stream : Type → Type
Stream a ≡ { head : a, tail : Stream a }
```

Generates:
1. Type constructor `Stream : Type → Type`
2. Record type expansion for type checking

```lean
def processCodataDecl (name : Ident) (params : List Ident) (sigs : List CopatSig) : InferM Unit := do
  -- Register type constructor
  let tyKind := params.foldr (fun _ k => .arrow .type k) .type
  addTypeCon name tyKind

  -- Convert copattern signatures to record field types
  let fields := sigs.map fun sig =>
    match sig.accessors with
    | [.field f] => (f, sig.ty)
    | [.apply x] => ("apply", .arrow (.var x) sig.ty)  -- callable codata
    | _ => panic! "nested copattern in declaration"

  -- Store as type alias: Stream a = { head : a, tail : Stream a }
  addTypeAlias name params (.record fields none)
```

When inferring `{ #.head => e₁, #.tail => e₂ } : Stream Int`:
1. Expand `Stream Int` to `{ head : Int, tail : Stream Int }`
2. Check each clause against the corresponding field type

---

## Part 10: Implementation Strategy

### Phase 1: Core HM (Current + Fixes)

1. Fix unification with proper occurs check
2. Implement proper substitution composition
3. Add let-polymorphism with generalization
4. Better error messages with source locations

### Phase 2: Patterns and Match

1. Implement pattern type inference
2. Add match expression inference
3. Pattern coverage warnings (optional)

### Phase 3: Records

1. Extend type language with row types
2. Implement row unification
3. Add record literal and field access inference

### Phase 4: Codata

1. Add codata type representation
2. Implement `#` scoping in codata blocks
3. Copattern type extraction
4. Mixed pattern/copattern inference

### Phase 5: Advanced Features

1. Sequent calculus (`cut`, `mu`)
2. Nested copatterns
3. Data/codata declarations
4. Module system integration

---

## Part 11: Data Structures

### Complete Type Definition

```lean
inductive Ty where
  | var     : Ident → Ty                           -- Type variable: α
  | con     : Ident → Ty                           -- Type constructor: Int, Bool, Stream
  | app     : Ty → Ty → Ty                         -- Type application: List α, Stream Int
  | arrow   : Ty → Ty → Ty                         -- Function type: α → β
  | forall_ : Ident → Ty → Ty                      -- Polymorphic: ∀α. τ
  | record  : List (Ident × Ty) → Option Ty → Ty   -- Record: { x : Int, y : Bool | ρ }

-- Note: No separate codata type constructor!
-- Codata blocks infer to record types (for field copatterns)
-- or function types (for application copatterns).

inductive Scheme where
  | mono   : Ty → Scheme
  | forall : List Ident → Ty → Scheme
```

### Inference State

```lean
structure InferState where
  nextVar   : Nat
  unionFind : UnionFind Ident Ty      -- Efficient unification
  typeEnv   : TyEnv                   -- Type environment
  errors    : List (SourcePos × String)

structure TyEnv where
  vars      : List (Ident × Scheme)   -- Term variable types
  typeCons  : List (Ident × Kind)     -- Type constructor kinds
  dataCons  : List (Ident × Scheme)   -- Data constructor types
  codataSigs: List (Ident × List CopatSig)  -- Codata observation types
```

### Union-Find for Efficient Unification

```lean
structure UnionFind where
  parent : HashMap Ident Ident
  rank   : HashMap Ident Nat
  repr   : HashMap Ident Ty           -- Representative type (if not variable)

def find (uf : UnionFind) (x : Ident) : Ident := ...
def union (uf : UnionFind) (x y : Ident) : UnionFind := ...
def bindVar (uf : UnionFind) (x : Ident) (t : Ty) : UnionFind := ...
```

---

## Summary

The type inference system for Ziku combines:

1. **Hindley-Milner core** with let-polymorphism
2. **Bidirectional checking** for codata blocks and patterns
3. **Row polymorphism** for flexible records
4. **Continuation typing** for sequent calculus features

### Key Design: Codata Types = Record/Function Types

The central insight is that **codata blocks infer to existing types**:

| Copattern Form | Inferred Type |
|----------------|---------------|
| `{ #.l₁ => e₁, ..., #.lₙ => eₙ }` | `{ l₁ : τ₁, ..., lₙ : τₙ }` (record) |
| `{ #(x) => e }` | `τ₁ → τ₂` (function) |
| `{ #(x)(y) => e }` | `τ₁ → τ₂ → τ₃` (curried function) |
| `{ #.f => e₁, #(x) => e₂ }` | `{ f : τ₁, apply : τ₂ → τ₃ }` (callable record) |

This eliminates the need for a separate `codata` type constructor while preserving the **duality**:
- **Data**: Constructed by constructors, destructed by patterns
- **Codata**: Constructed by copattern blocks, destructed by field access/application

### Key Mechanisms

- **`#` in expression position**: Typed as the enclosing codata block's type (recursive reference)
- **Nested copatterns**: Elaborated into nested codata blocks before type checking
- **Mixed patterns/copatterns**: Patterns determine argument types, copatterns determine result structure
- **Codata declarations**: Introduce type aliases equivalent to record types

This design maintains principal types while supporting Ziku's unique codata-centric features.
