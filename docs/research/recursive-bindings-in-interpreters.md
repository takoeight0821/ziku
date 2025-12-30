# Recursive Bindings Implementation in Functional Language Interpreters

## Overview

This document explores techniques for implementing recursive bindings (`letrec`) in functional language interpreters, particularly in strict/call-by-value languages like Lean 4.

## The Problem

The semantic goal of `letrec` is that the right-hand side of bindings are evaluated in an environment that **already includes the bindings**. This creates a chicken-and-egg problem: we cannot create such an environment because we haven't yet computed the values.

The current Ziku implementation uses a static iteration count to "unroll" recursion:

```lean
-- Current approach (Ziku/IR/Eval.lean:141-156)
let p1 := p.substVar x p
let p2 := p1.substVar x p1
-- ... 10 iterations
let p10 := p9.substVar x p9
some (s.substVar x p10)
```

This is fundamentally broken because:
1. It limits recursion depth arbitrarily
2. It causes exponential growth in term size
3. It doesn't correctly model the semantics of recursive bindings

## Implementation Approaches

### 1. Lazy Evaluation / Thunks (Recommended for Ziku)

In lazy languages like Haskell, "tying the knot" works naturally:

```haskell
-- Haskell: lazy evaluation makes this work
let x = 0 : y
    y = 1 : x
in x  -- infinite cyclic list
```

For strict languages, we can simulate laziness with explicit thunks:

```lean
-- Lean 4: Thunk-based approach
inductive Value where
  | thunk : (Unit → Value) → Value
  | lit : Lit → Value
  | closure : Env → Ident → Expr → Value

def force : Value → Value
  | .thunk f => f ()
  | v => v
```

**Key insight**: Laziness allows us to create pointers to values that don't yet exist. When we construct a recursive data structure, we don't need to know the value of the reference immediately—we just need a pointer to where we can eventually find it.

**References**:
- [HaskellWiki: Tying the Knot](https://wiki.haskell.org/Tying_the_Knot)
- [Guerric Chupin: Tying the knot in Haskell, OCaml and Idris](https://typochon.chnik.fr/posts/tying-the-knot/)

### 2. Mutable References / Backpatching

The standard approach in strict languages is backpatching:

1. Allocate a mutable cell for each recursive variable, initialized to "undefined"
2. Evaluate the right-hand sides in the extended environment
3. Update (backpatch) the cells with the computed values

```typescript
// Backpatching approach (from BGU PL course)
const evalLetrec = (exp: LetrecExp, env: Env): Result<Value> => {
    const vars = map((b: Binding) => b.var.var, exp.bindings);
    const vals = map((b: Binding) => b.val, exp.bindings);
    // Phase 1: Create environment with undefined placeholders
    const extEnv = makeExtEnv(vars, repeat(undefined, vars.length), env);
    // Phase 2: Evaluate in extended environment
    const cvalsResult = mapResult((v: CExp) =>
        applicativeEval(v, extEnv), vals);
    // Phase 3: Update bindings with computed values
    return bind(result, _ => evalSequence(exp.body, extEnv));
};
```

For Lean 4 with `IO` monad:

```lean
-- Lean 4: Mutable reference approach
structure Env where
  bindings : HashMap Ident (IO.Ref (Option Value))

def evalLetRec (bindings : List (Ident × Expr)) (body : Expr) (env : Env) : IO Value := do
  -- Phase 1: Create refs with None
  let refs ← bindings.mapM fun (x, _) => do
    let r ← IO.mkRef none
    pure (x, r)
  let extEnv := refs.foldl (fun e (x, r) => e.insert x r) env

  -- Phase 2: Evaluate and backpatch
  for (x, expr) in bindings do
    let v ← eval expr extEnv
    let r := extEnv.find! x
    r.set (some v)

  -- Phase 3: Evaluate body
  eval body extEnv
```

**References**:
- [BGU: Recursion and Mutation](https://bguppl.github.io/interpreters/class_material/2.8RecursionMutation.html)
- [Derek Dreyer's Thesis Chapter 5: The Recursive Module Problem](https://people.mpi-sws.org/~dreyer/courses/modules/dreyer-thesis-chapter5.pdf)

### 3. Recursive Environment (rec-env)

Store closures **without** their environment reference, then construct the full closure at lookup time:

```lean
-- Recursive environment approach
inductive Env where
  | empty
  | ext : Ident → Value → Env → Env
  | rec : Ident → List Ident → Expr → Env → Env  -- delayed closure

def lookup (x : Ident) : Env → Option Value
  | .empty => none
  | .ext y v env => if x == y then some v else lookup x env
  | .rec f params body env =>
    if x == f then
      -- Construct closure at lookup time with current (recursive) env
      some (.closure (Env.rec f params body env) params body)
    else lookup x env
```

**Key insight**: By delaying closure construction until lookup, the closure captures the recursive environment.

### 4. Fixpoint Combinator (Pure Functional)

For pure functional implementations without mutation, use a fixpoint combinator:

```lean
-- Strict fixpoint combinator
partial def fix {α β : Type} (f : (α → β) → α → β) (x : α) : β :=
  f (fix f) x

-- Polyvariadic fix for mutual recursion
partial def fixPoly {α β : Type}
    (clauses : List ((List (α → β)) → α → β)) : List (α → β) :=
  clauses.map fun clause x => clause (fixPoly clauses) x
```

**OCaml implementation**:
```ocaml
let rec fix : (('a -> 'b) -> ('a -> 'b)) -> ('a -> 'b) =
  fun f x -> f (fix f) x

let fix_poly : (('a -> 'b) list -> 'a -> 'b) list -> ('a -> 'b) list =
  fun l -> fix (fun self l -> List.map (fun li x -> li (self l) x) l) l
```

**References**:
- [okmij.org: Many faces of the fixed-point combinator](https://www.okmij.org/ftp/Computation/fixed-point-combinators.html)
- [Wikipedia: Fixed-point combinator](https://en.wikipedia.org/wiki/Fixed-point_combinator)

### 5. Graph Reduction / Heap-based Evaluation

Model sharing explicitly through a heap/graph structure:

```lean
-- Heap-based approach
structure Heap where
  cells : HashMap Nat HeapCell
  nextAddr : Nat

inductive HeapCell where
  | thunk : Expr → Env → HeapCell
  | value : Value → HeapCell
  | blackhole : HeapCell  -- for detecting circular evaluation

inductive Value where
  | ref : Nat → Value  -- pointer into heap
  | lit : Lit → Value
  | ...
```

For `letrec`, allocate heap cells for all bindings first (as thunks or blackholes), then evaluate. This naturally handles mutual recursion and sharing.

**References**:
- [Call-by-Need Lambda Calculus (Ariola & Felleisen)](https://www.researchgate.net/publication/2597124_A_Call-By-Need_Lambda_Calculus)
- [Small-step and big-step semantics for call-by-need](https://cs.ioc.ee/~keiko/papers/petitcbn.pdf)

## Recommendation for Ziku

Given Ziku's sequent calculus IR and the λμμ̃-calculus foundation, I recommend **Option 1 (Thunks) combined with Option 5 (Heap-based)**:

### Proposed Design

1. **Introduce a heap/store** to the evaluation state:

```lean
structure EvalState where
  heap : HashMap Nat HeapCell
  nextAddr : Nat

inductive HeapCell where
  | thunk : Statement → HeapCell     -- unevaluated
  | value : Producer → HeapCell      -- fully evaluated
  | blackhole : HeapCell             -- being evaluated (cycle detection)
```

2. **Modify `Producer` to include heap references**:

```lean
inductive Producer where
  | var : SourcePos → Ident → Producer
  | ref : SourcePos → Nat → Producer  -- NEW: heap reference
  | lit : SourcePos → Lit → Producer
  | mu : SourcePos → Ident → Statement → Producer
  | cocase : SourcePos → List (Ident × List Ident × Statement) → Producer
  | record : SourcePos → List (Ident × Producer) → Producer
```

3. **Implement μ̃-reduction with delayed substitution**:

```lean
-- For ⟨v | μ̃x.s⟩ where v is a recursive value:
-- 1. Allocate a heap cell for x
-- 2. Store v (possibly containing refs to x) in the cell
-- 3. Evaluate s with x bound to the heap reference
```

4. **Translate `letRec` to use heap allocation**:

```
⟦let rec x = e₁ in e₂⟧ =
  μα. alloc(addr).        -- allocate heap cell
      ⟨⟦e₁⟧[ref(addr)/x] | store(addr; μ̃_.⟨⟦e₂⟧ | α⟩)⟩
```

### Benefits

- **Correct semantics**: Properly handles arbitrary recursion depth
- **No exponential blowup**: Uses indirection instead of term expansion
- **Cycle detection**: Blackhole cells detect infinite loops during evaluation
- **Matches theory**: Aligns with call-by-need semantics literature

## Academic References

### Core Papers

1. **Fixing Letrec** - Waddell, Sarkar & Dybvig
   - [PDF (Tufts)](https://www.cs.tufts.edu/comp/150VM/modules/archive/kent-dybvig/letrec.pdf)
   - Describes efficient compilation of `letrec` preserving R5RS semantics

2. **A Call-By-Need Lambda Calculus** - Ariola & Felleisen (1997)
   - [ResearchGate](https://www.researchgate.net/publication/2597124_A_Call-By-Need_Lambda_Calculus)
   - Foundational semantics for lazy evaluation with sharing

3. **Denotational semantics for lazy initialization of letrec** - Nakata et al.
   - [PDF](https://cs.ioc.ee/~keiko/papers/fics10.pdf)
   - Formal semantics for `letrec` in call-by-value with laziness

4. **Superdeduction in Lambda-Bar-Mu-Mu-Tilde**
   - [arXiv:1101.5443](https://arxiv.org/abs/1101.5443)
   - Extension of λμμ̃-calculus

### Textbooks and Courses

- [BGU: Recursion and Mutation](https://bguppl.github.io/interpreters/class_material/2.8RecursionMutation.html)
- [Cornell CS 4110: Denotational Semantics](https://www.cs.cornell.edu/courses/cs4110/2016fa/lectures/lecture08.pdf)
- [Real World OCaml: Imperative Programming](https://dev.realworldocaml.org/imperative-programming.html)

## Summary

| Approach | Purity | Complexity | Correctness | Best For |
|----------|--------|------------|-------------|----------|
| Static unrolling | Pure | O(n²) | Limited | Never use |
| Thunks | Pure | O(n) | Correct | Simple cases |
| Backpatching | Impure | O(n) | Correct | Production interpreters |
| rec-env | Pure | O(n) | Correct | Teaching |
| Fixpoint combinator | Pure | O(n) | Correct | Theory |
| Heap/Graph | Impure | O(n) | Correct | Call-by-need |

**Key takeaway**: The current static iteration approach cannot correctly implement recursive bindings. Use thunks/lazy evaluation or mutable references with backpatching.
