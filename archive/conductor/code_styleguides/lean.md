# Lean 4 Coding Guide

A comprehensive style guide for writing clear, maintainable, and idiomatic Lean 4 code.

---

## Naming Conventions

### General Principles

Use `lowerCamelCase` for definitions, theorems, and lemmas. Use `UpperCamelCase` for types, structures, and inductive types.

```lean
-- Types and structures
structure NatPair where
  fst : Nat
  snd : Nat

inductive BinaryTree (α : Type) where
  | leaf : BinaryTree α
  | node : BinaryTree α → α → BinaryTree α → BinaryTree α

-- Definitions and functions
def listLength : List α → Nat
  | [] => 0
  | _ :: xs => 1 + listLength xs

-- Theorems and lemmas
theorem addComm (n m : Nat) : n + m = m + n := Nat.add_comm n m
```

### Naming Patterns

Follow Mathlib conventions for theorem names. Use dots to indicate namespacing and underscores within logical units.

```lean
-- Pattern: [namespace].[type]_[property]_[qualifier]
theorem List.length_append (xs ys : List α) : (xs ++ ys).length = xs.length + ys.length := ...
theorem Nat.add_comm (n m : Nat) : n + m = m + n := ...
theorem Nat.mul_add_one (n m : Nat) : n * (m + 1) = n * m + n := ...

-- Predicates: use "is" or "has" prefix
def List.isEmpty : List α → Bool
def Nat.isEven : Nat → Bool
def Graph.hasPath : Graph → Vertex → Vertex → Prop
```

### Abbreviations

Avoid abbreviations unless they are universally understood in the domain.

```lean
-- Good
def numberOfElements : List α → Nat := List.length
def coefficient : Polynomial → Nat → Int := ...

-- Acceptable (domain-standard)
def gcd : Nat → Nat → Nat := Nat.gcd
def lcm : Nat → Nat → Nat := Nat.lcm

-- Avoid
def numElems : List α → Nat := ...  -- unclear abbreviation
def coef : Polynomial → Nat → Int := ...
```

---

## Formatting

### Indentation

Use 2 spaces for indentation. Never use tabs.

```lean
def factorial : Nat → Nat
  | 0 => 1
  | n + 1 => (n + 1) * factorial n

structure Point where
  x : Float
  y : Float
  deriving Repr, BEq
```

### Line Length

Keep lines under 100 characters. Break long lines at logical points.

```lean
-- Good: break after arrows and at logical boundaries
def veryLongFunctionName
    (firstParameter : SomeType)
    (secondParameter : AnotherType)
    (thirdParameter : YetAnotherType) :
    ResultType :=
  computeResult firstParameter secondParameter thirdParameter

-- Good: break long type signatures
theorem someComplexTheorem
    (h₁ : Condition1)
    (h₂ : Condition2)
    (h₃ : Condition3) :
    Conclusion := by
  sorry
```

### Blank Lines

Use blank lines to separate logical sections. Use one blank line between top-level declarations.

```lean
namespace MyModule

def helper1 : Nat → Nat := fun n => n + 1

def helper2 : Nat → Nat := fun n => n * 2

/-- Main function that combines helpers. -/
def mainFunction (n : Nat) : Nat :=
  helper2 (helper1 n)

end MyModule
```

### Alignment

Align similar elements vertically when it improves readability.

```lean
structure Config where
  maxIterations : Nat     := 1000
  tolerance     : Float   := 0.001
  verbose       : Bool    := false
  outputPath    : String  := "./output"
```

---

## Type Annotations

### When to Include Types

Always annotate top-level definitions. Omit types for local bindings when obvious.

```lean
-- Always annotate top-level definitions
def square (n : Nat) : Nat := n * n

-- Omit for obvious local bindings
def sumSquares (xs : List Nat) : Nat :=
  xs.foldl (fun acc x => acc + x * x) 0
  --           ^^^----- type is clear from context

-- Include when it aids readability or disambiguation
def processData (data : List α) [BEq α] : List α :=
  let unique : List α := data.eraseDups  -- helpful annotation
  unique.reverse
```

### Implicit vs Explicit Arguments

Use implicit arguments `{α : Type}` for types that can be inferred. Use instance arguments `[inst : Class α]` for type classes.

```lean
-- Implicit type parameter (inferred from usage)
def identity {α : Type} (x : α) : α := x

-- Instance argument for type class
def compare [Ord α] (x y : α) : Ordering := Ord.compare x y

-- Explicit when caller should specify
def replicate (n : Nat) (α : Type) (x : α) : List α :=
  List.replicate n x
```

---

## Functions and Definitions

### Pattern Matching

Prefer top-level pattern matching over `match` expressions for simple cases.

```lean
-- Good: top-level patterns
def length : List α → Nat
  | [] => 0
  | _ :: xs => 1 + length xs

-- Good: match for complex or nested patterns
def findFirst (p : α → Bool) (xs : List α) : Option α :=
  match xs with
  | [] => none
  | x :: xs =>
    if p x then some x
    else findFirst p xs

-- Avoid: unnecessary match
def lengthBad (xs : List α) : Nat :=
  match xs with  -- prefer top-level patterns
  | [] => 0
  | _ :: xs => 1 + lengthBad xs
```

### Lambda Expressions

Use `fun` for lambdas. Use `·` notation for simple point-free expressions.

```lean
-- Full lambda syntax
def addOne : Nat → Nat := fun n => n + 1

-- Point-free with ·
def doubled : List Nat → List Nat := List.map (· * 2)

-- Multiple arguments
def add : Nat → Nat → Nat := fun x y => x + y

-- Avoid mixing styles inconsistently
def process := List.map (fun x => x + 1)  -- or List.map (· + 1), not both
```

### Recursion

Use structural recursion when possible. Use `termination_by` for non-structural recursion.

```lean
-- Structural recursion (preferred)
def sum : List Nat → Nat
  | [] => 0
  | x :: xs => x + sum xs

-- Non-structural with termination proof
def gcd (m n : Nat) : Nat :=
  if n = 0 then m
  else gcd n (m % n)
termination_by n
decreasing_by
  simp_wf
  omega

-- Tail recursion with accumulator
def sumTR (xs : List Nat) : Nat :=
  go xs 0
where
  go : List Nat → Nat → Nat
    | [], acc => acc
    | x :: xs, acc => go xs (acc + x)
```

---

## Structures and Inductive Types

### Structure Definitions

Use the `where` syntax for structures. Include default values when sensible.

```lean
structure ServerConfig where
  host : String := "localhost"
  port : Nat := 8080
  maxConnections : Nat := 100
  timeout : Nat := 30
  deriving Repr, BEq

-- Construction
def defaultConfig : ServerConfig := {}
def customConfig : ServerConfig := { port := 3000, maxConnections := 50 }

-- Field access and update
def withPort (cfg : ServerConfig) (p : Nat) : ServerConfig :=
  { cfg with port := p }
```

### Inductive Types

Align constructors and include type annotations for clarity.

```lean
inductive Expr where
  | const : Int → Expr
  | var   : String → Expr
  | add   : Expr → Expr → Expr
  | mul   : Expr → Expr → Expr
  | neg   : Expr → Expr
  deriving Repr, BEq

-- Recursive functions over inductives
def eval (env : String → Int) : Expr → Int
  | .const n => n
  | .var name => env name
  | .add e₁ e₂ => eval env e₁ + eval env e₂
  | .mul e₁ e₂ => eval env e₁ * eval env e₂
  | .neg e => -(eval env e)
```

### Type Classes

Define instances in the same file as the type when possible.

```lean
class Monoid (α : Type) where
  unit : α
  op : α → α → α
  op_assoc : ∀ a b c, op (op a b) c = op a (op b c)
  unit_op : ∀ a, op unit a = a
  op_unit : ∀ a, op a unit = a

instance : Monoid Nat where
  unit := 0
  op := (· + ·)
  op_assoc := Nat.add_assoc
  unit_op := Nat.zero_add
  op_unit := Nat.add_zero
```

---

## Tactics and Proofs

### Tactic Style

Use structured proofs with proper indentation. Prefer term-mode for simple proofs.

```lean
-- Term mode for simple proofs
theorem add_zero (n : Nat) : n + 0 = n := Nat.add_zero n

-- Tactic mode for complex proofs
theorem list_reverse_reverse (xs : List α) : xs.reverse.reverse = xs := by
  induction xs with
  | nil => rfl
  | cons x xs ih =>
    simp [List.reverse_cons]
    exact ih

-- Structured proof with clear steps
theorem sqrt_two_irrational : ¬∃ (p q : Nat), q ≠ 0 ∧ p^2 = 2 * q^2 := by
  intro ⟨p, q, hq, h⟩
  -- Proof proceeds by infinite descent
  sorry
```

### Proof Organization

Break complex proofs into `have` and `suffices` statements.

```lean
theorem complex_theorem (n : Nat) (h : n > 0) : SomeProperty n := by
  -- State intermediate goals clearly
  have h1 : IntermediateProperty1 n := by
    sorry
  have h2 : IntermediateProperty2 n := by
    sorry
  -- Combine to conclude
  exact combine_properties h1 h2
```

### Common Tactics

```lean
-- Simplification
simp                    -- automatic simplification
simp only [lemma1, lemma2]  -- controlled simplification
simp [*, h]             -- include hypotheses

-- Case analysis
cases h                 -- destruct hypothesis
rcases h with ⟨a, b, c⟩ -- recursive cases with patterns
obtain ⟨x, hx⟩ := h     -- extract witness

-- Rewriting
rw [eq1, eq2]           -- rewrite left to right
rw [← eq1]              -- rewrite right to left
conv => ...             -- targeted rewriting

-- Automation
omega                   -- linear arithmetic
decide                  -- decidable propositions
native_decide           -- use native code
aesop                   -- general automation
```

---

## Documentation

### Doc Comments

Use `/-- -/` for documentation comments. Place them immediately before the definition.

```lean
/-- Computes the factorial of a natural number.

The factorial of `n`, written `n!`, is defined as:
- `0! = 1`
- `(n+1)! = (n+1) * n!`

## Examples
```

#eval factorial 5 -- 120
#eval factorial 0 -- 1

```
-/
def factorial : Nat → Nat
  | 0 => 1
  | n + 1 => (n + 1) * factorial n
```

### Module Documentation

Include a module docstring at the top of each file.

```lean
/-!
# List Operations

This module provides additional operations on lists, including
efficient concatenation and various folding operations.

## Main Definitions

* `List.fastConcat` - O(1) concatenation using difference lists
* `List.foldlM` - monadic left fold

## Implementation Notes

The `fastConcat` operation uses continuation-passing style internally
to achieve constant-time concatenation.
-/

namespace List

-- definitions follow...

end List
```

### Inline Comments

Use `--` for inline comments. Keep them concise and meaningful.

```lean
def binarySearch (arr : Array α) [Ord α] (target : α) : Option Nat :=
  go 0 arr.size
where
  go (lo hi : Nat) : Option Nat :=
    if lo >= hi then none
    else
      let mid := (lo + hi) / 2  -- avoid overflow for large arrays
      match compare arr[mid]! target with
      | .lt => go (mid + 1) hi
      | .gt => go lo mid
      | .eq => some mid
  termination_by hi - lo
```

---

## Imports and Namespaces

### Import Organization

Group imports logically: standard library, Mathlib, local modules.

```lean
-- Standard library
import Lean
import Init.Data.Array

-- External libraries (Mathlib)
import Mathlib.Data.List.Basic
import Mathlib.Algebra.Group.Basic

-- Local project modules
import MyProject.Utils
import MyProject.Core
```

### Namespace Usage

Use namespaces to organize related definitions. Open namespaces judiciously.

```lean
namespace MyProject.DataStructures

-- All definitions here are in MyProject.DataStructures

def Stack := List

def Stack.push (s : Stack α) (x : α) : Stack α := x :: s

def Stack.pop : Stack α → Option (α × Stack α)
  | [] => none
  | x :: xs => some (x, xs)

end MyProject.DataStructures

-- Selective opening
open MyProject.DataStructures (Stack)

-- Scoped opening
section
open List in
def example := [1, 2, 3].reverse
end
```

---

## Error Handling

### Option and Except

Use `Option` for simple failure cases. Use `Except` for errors with information.

```lean
-- Option for simple lookup
def findIndex (p : α → Bool) (xs : List α) : Option Nat :=
  xs.findIdx? p

-- Except for detailed errors
inductive ParseError
  | unexpectedChar (c : Char) (pos : Nat)
  | unexpectedEOF
  | invalidNumber (s : String)

def parseNumber (s : String) : Except ParseError Nat := do
  if s.isEmpty then throw .unexpectedEOF
  let digits ← s.toList.mapM fun c =>
    if c.isDigit then pure (c.toNat - '0'.toNat)
    else throw (.unexpectedChar c 0)
  pure (digits.foldl (· * 10 + ·) 0)
```

### Monadic Error Handling

Use `do` notation for clean error propagation.

```lean
def processFile (path : String) : IO (Except String Data) := do
  let contents ← IO.FS.readFile path
  let parsed ← match parse contents with
    | .ok data => pure data
    | .error e => return .error s!"Parse error: {e}"
  let validated ← match validate parsed with
    | .ok data => pure data
    | .error e => return .error s!"Validation error: {e}"
  return .ok validated
```

---

## Performance Considerations

### Array vs List

Use `Array` for random access and mutation. Use `List` for sequential processing and pattern matching.

```lean
-- Array for indexed access
def sumArray (arr : Array Nat) : Nat := Id.run do
  let mut sum := 0
  for x in arr do
    sum := sum + x
  return sum

-- List for recursive processing
def filterList (p : α → Bool) : List α → List α
  | [] => []
  | x :: xs => if p x then x :: filterList p xs else filterList p xs
```

### Avoiding Recomputation

Use `let` bindings to avoid repeated computation.

```lean
-- Good: compute once
def process (x : Nat) : Nat :=
  let expensive := veryExpensiveComputation x
  expensive + expensive * 2

-- Avoid: recomputes
def processBad (x : Nat) : Nat :=
  veryExpensiveComputation x + veryExpensiveComputation x * 2
```

---

## Testing

### Unit Tests

Use `#guard` and `#check_failure` for compile-time tests.

```lean
#guard factorial 5 = 120
#guard factorial 0 = 1
#guard [1, 2, 3].reverse = [3, 2, 1]

-- Test that something fails to typecheck
-- #check_failure (true + false)
```

### Property-Based Testing

Use `#eval` with assertions for runtime verification.

```lean
#eval do
  for n in [0:100] do
    let result := factorial n
    assert! result > 0
  IO.println "All tests passed!"
```

---

## Project Structure

### Recommended Layout

```
MyProject/
├── MyProject.lean           -- Main import file
├── MyProject/
│   ├── Basic.lean           -- Core definitions
│   ├── Data/
│   │   ├── List.lean        -- List extensions
│   │   └── Array.lean       -- Array extensions
│   ├── Tactic/
│   │   └── Custom.lean      -- Custom tactics
│   └── Meta/
│       └── Elaborator.lean  -- Metaprogramming
├── lakefile.lean            -- Build configuration
└── lean-toolchain           -- Lean version
```

### Module Dependencies

Keep dependencies acyclic. Use forward declarations if necessary.

```lean
-- In MyProject.lean (root)
import MyProject.Basic
import MyProject.Data.List
import MyProject.Data.Array
import MyProject.Tactic.Custom
```

---

## Metaprogramming

### Syntax Extensions

Define clear syntax with proper documentation.

```lean
/-- Syntax for list comprehension: `[x * 2 | x ← xs, x > 0]` -/
syntax "[" term "|" ident "←" term ("," term)* "]" : term

macro_rules
  | `([$body | $x ← $xs]) => `(List.map (fun $x => $body) $xs)
  | `([$body | $x ← $xs, $pred]) =>
    `(List.filterMap (fun $x => if $pred then some $body else none) $xs)
```

### Custom Tactics

Use `elab` for complex tactics, `macro` for simple syntactic transforms.

```lean
/-- Tactic that applies `simp` then `rfl`. -/
macro "simp_rfl" : tactic => `(tactic| simp; rfl)

/-- Tactic that tries multiple approaches. -/
elab "auto" : tactic => do
  let goal ← Lean.Elab.Tactic.getMainGoal
  -- Try different strategies
  try Lean.Elab.Tactic.evalTactic (← `(tactic| decide))
  catch _ =>
    try Lean.Elab.Tactic.evalTactic (← `(tactic| simp))
    catch _ =>
      Lean.Elab.Tactic.evalTactic (← `(tactic| rfl))
```

---

## Summary Checklist

- [ ] Use `lowerCamelCase` for functions, `UpperCamelCase` for types
- [ ] Follow Mathlib naming conventions for theorems
- [ ] Keep lines under 100 characters
- [ ] Use 2-space indentation consistently
- [ ] Always annotate top-level definitions
- [ ] Prefer structural recursion
- [ ] Document all public definitions
- [ ] Use `Option` / `Except` for error handling
- [ ] Choose `Array` vs `List` appropriately
- [ ] Include tests with `#guard` and `#eval`
