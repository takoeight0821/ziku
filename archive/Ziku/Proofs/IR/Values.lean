import Ziku.IR.Syntax

namespace Ziku.Proofs.IR

/-!
# Value Definitions for IR

This module defines values (terminal producers) as inductive relations.
These definitions formalize the `isTerminal` and `isSimpleValue` functions
from `Ziku/IR/Eval.lean`.

## Correspondence with Implementation

| Proof Definition | Implementation (IR/Eval.lean) |
|------------------|-------------------------------|
| `IsValue`        | `Producer.isTerminal`         |
| `IsSimpleValue`  | `Producer.isSimpleValue`      |

The key difference is that the implementation uses `partial def` with `Bool`,
while this module uses inductive propositions (`Prop`) that can be used in proofs.
-/

open Ziku (SourcePos Ident Lit)
open Ziku.IR (Producer Consumer Statement)

/-- A producer is a value (terminal) if it cannot be further reduced.
    This corresponds to `Producer.isTerminal` in `Ziku/IR/Eval.lean:161-168`.

    Terminal producers are:
    - Literals (int, bool, string, etc.)
    - Cocase blocks (codata constructors)
    - Records
    - Data constructors where all arguments are values
-/
inductive IsValue : Producer → Prop where
  /-- Literal values are terminal.
      Corresponds to `IR/Eval.lean:163`: `.lit _ _ => true` -/
  | lit : ∀ pos l, IsValue (.lit pos l)
  /-- Cocase (codata constructor) is terminal.
      Corresponds to `IR/Eval.lean:165`: `.cocase _ _ => true` -/
  | cocase : ∀ pos branches, IsValue (.cocase pos branches)
  /-- Record is terminal.
      Corresponds to `IR/Eval.lean:166`: `.record _ _ => true` -/
  | record : ∀ pos fields, IsValue (.record pos fields)
  /-- Data constructor is terminal when all arguments are values.
      Corresponds to `IR/Eval.lean:168`: `.dataCon _ _ args => args.all Producer.isTerminal` -/
  | dataCon : ∀ pos con args,
      (∀ arg, arg ∈ args → IsValue arg) →
      IsValue (.dataCon pos con args)

/-- A producer is a simple value if it doesn't need an environment
    for its evaluation. This corresponds to `Producer.isSimpleValue`
    in `Ziku/IR/Eval.lean:173-176`.

    Simple values are:
    - Literals
    - Data constructors where all arguments are simple values
-/
inductive IsSimpleValue : Producer → Prop where
  /-- Literal values are simple.
      Corresponds to `IR/Eval.lean:174`: `.lit _ _ => true` -/
  | lit : ∀ pos l, IsSimpleValue (.lit pos l)
  /-- Data constructor is simple when all arguments are simple.
      Corresponds to `IR/Eval.lean:175`: `.dataCon _ _ args => args.all Producer.isSimpleValue` -/
  | dataCon : ∀ pos con args,
      (∀ arg, arg ∈ args → IsSimpleValue arg) →
      IsSimpleValue (.dataCon pos con args)

-- Basic lemmas about values

/-- Simple values are also values. -/
theorem IsSimpleValue.isValue : ∀ p, IsSimpleValue p → IsValue p := by
  intro p hsimple
  induction hsimple with
  | lit pos l => exact IsValue.lit pos l
  | dataCon pos con args hargs ih =>
    apply IsValue.dataCon
    intro arg harg
    exact ih arg harg

/-- Variables are not values. -/
theorem var_not_value : ∀ pos x, ¬IsValue (.var pos x) := by
  intro pos x h
  cases h

/-- Mu abstractions are not values. -/
theorem mu_not_value : ∀ pos α s, ¬IsValue (.mu pos α s) := by
  intro pos α s h
  cases h

/-- Fix expressions are not values. -/
theorem fix_not_value : ∀ pos x body, ¬IsValue (.fix pos x body) := by
  intro pos x body h
  cases h

/-- Empty data constructor is a value. -/
theorem dataCon_empty_is_value : ∀ pos con, IsValue (.dataCon pos con []) := by
  intro pos con
  apply IsValue.dataCon
  intro arg harg
  cases harg

/-- Data constructor with single literal argument is a value. -/
theorem dataCon_single_lit_is_value : ∀ pos con litPos l,
    IsValue (.dataCon pos con [.lit litPos l]) := by
  intro pos con litPos l
  apply IsValue.dataCon
  intro arg harg
  cases harg with
  | head => exact IsValue.lit litPos l
  | tail _ h => cases h

end Ziku.Proofs.IR
