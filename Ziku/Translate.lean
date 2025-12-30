import Ziku.Syntax
import Ziku.IR.Syntax
import Ziku.IR.Eval

namespace Ziku.Translate

/-!
# Surface → IR Translation

Translates surface language expressions to sequent calculus IR.

Based on "Grokking the Sequent Calculus" (ICFP 2024).

## Translation Rules

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
-/

open Ziku (SourcePos Ident BinOp UnaryOp Lit Expr)
open Ziku.IR (Producer Consumer Statement)

-- Translation state
structure TranslateState where
  freshCounter : Nat := 0
  labelScope : List Ident := []  -- Valid label names in scope
  deriving Inhabited

-- Translation errors
inductive TranslateError where
  | undefinedLabel (pos : SourcePos) (name : Ident)
  | notImplemented (pos : SourcePos) (feature : String)
  deriving Repr

def TranslateError.toString : TranslateError → String
  | .undefinedLabel pos name => s!"Undefined label '{name}' at {pos.line}:{pos.col}"
  | .notImplemented pos feature => s!"Translation not implemented for {feature} at {pos.line}:{pos.col}"

instance : ToString TranslateError := ⟨TranslateError.toString⟩

-- Translation monad
abbrev TranslateM := StateT TranslateState (Except TranslateError)

-- Inhabited instance for partial functions
instance : Inhabited (TranslateM Producer) where
  default := throw (.notImplemented { line := 0, col := 0 } "uninhabited")

-- Generate fresh covariable name
def freshCovar : TranslateM Ident := do
  let s ← get
  let name := s!"_α{s.freshCounter}"
  set { s with freshCounter := s.freshCounter + 1 }
  return name

-- Check if label is in scope
def isLabelInScope (name : Ident) : TranslateM Bool := do
  let s ← get
  return s.labelScope.contains name

-- Add label to scope
def withLabel (name : Ident) (m : TranslateM α) : TranslateM α := do
  let s ← get
  set { s with labelScope := name :: s.labelScope }
  let result ← m
  let s' ← get
  set { s' with labelScope := s.labelScope }
  return result

-- Dummy position for generated code
def dummyPos : SourcePos := { line := 0, col := 0 }

/-
Translation produces a Producer in most cases.
The key insight from Grokking is that surface expressions are producers,
and we use μ to capture the continuation context.
-/

mutual
  -- Translate expression to Producer
  partial def translateExpr (e : Expr) : TranslateM Producer :=
    match e with
    | .lit pos l => return .lit pos l
    | .var pos x => return .var pos x
    | .binOp pos op e1 e2 => do
      -- ⟦t₁ ⊙ t₂⟧ = μα. ⊙(⟦t₁⟧, ⟦t₂⟧; α)
      let α ← freshCovar
      let p1 ← translateExpr e1
      let p2 ← translateExpr e2
      return .mu pos α (.binOp pos op p1 p2 (.covar dummyPos α))
    | .unaryOp pos op e => do
      -- Translate unary as binary with dummy
      throw $ .notImplemented pos "unary operator translation"
    | .lam pos param body => do
      -- ⟦λx.t⟧ = cocase {ap(x; α) ⇒ ⟨⟦t⟧ | α⟩}
      let α ← freshCovar
      let bodyP ← translateExpr body
      return .cocase pos [("ap", [param, α], .cut dummyPos bodyP (.covar dummyPos α))]
    | .app pos fn arg => do
      -- ⟦t₁ t₂⟧ = μα.⟨⟦t₁⟧ | ap(⟦t₂⟧; α)⟩
      let α ← freshCovar
      let fnP ← translateExpr fn
      let argP ← translateExpr arg
      return .mu pos α (.cut dummyPos fnP (.destructor dummyPos "ap" [argP] (.covar dummyPos α)))
    | .let_ pos x _ e1 e2 => do
      -- ⟦let x = t₁ in t₂⟧ = μα.⟨⟦t₁⟧ | μ̃x.⟨⟦t₂⟧ | α⟩⟩
      let α ← freshCovar
      let p1 ← translateExpr e1
      let p2 ← translateExpr e2
      return .mu pos α (.cut dummyPos p1 (.muTilde dummyPos x (.cut dummyPos p2 (.covar dummyPos α))))
    | .letRec pos x _ e1 e2 => do
      -- ⟦let rec x = e₁ in e₂⟧ = μα.⟨⟦e₁⟧[⟦e₁⟧/x] | μ̃x.⟨⟦e₂⟧ | α⟩⟩
      -- Pre-substitute x in e1 to handle recursion (works because cocase guards the body)
      let α ← freshCovar
      let p1 ← translateExpr e1
      -- Substitute p1 for x in p1 itself to create self-reference
      let p1' := IR.Producer.substVar x p1 p1
      let p2 ← translateExpr e2
      return .mu pos α (.cut dummyPos p1' (.muTilde dummyPos x (.cut dummyPos p2 (.covar dummyPos α))))
    | .if_ pos cond thenE elseE => do
      -- ⟦if t₁ then t₂ else t₃⟧ = μα.ifz(⟦t₁⟧, ⟨⟦t₂⟧ | α⟩, ⟨⟦t₃⟧ | α⟩)
      let α ← freshCovar
      let condP ← translateExpr cond
      let thenP ← translateExpr thenE
      let elseP ← translateExpr elseE
      return .mu pos α (.ifz dummyPos condP
        (.cut dummyPos thenP (.covar dummyPos α))
        (.cut dummyPos elseP (.covar dummyPos α)))
    | .match_ pos _ _ => do
      throw $ .notImplemented pos "match expression"
    | .codata pos _ => do
      throw $ .notImplemented pos "codata block"
    | .field pos e fieldName => do
      -- ⟦e.f⟧ = μα.⟨⟦e⟧ | f(; α)⟩
      let α ← freshCovar
      let prodE ← translateExpr e
      return .mu pos α (.cut dummyPos prodE (.destructor dummyPos fieldName [] (.covar dummyPos α)))
    | .ann _ e _ => translateExpr e  -- Ignore type annotations
    | .record pos fields => do
      -- ⟦{ f₁ = e₁, ... }⟧ = { f₁ = ⟦e₁⟧, ... }
      let fields' ← fields.mapM (fun (name, e) => do
        let p ← translateExpr e
        pure (name, p))
      return .record pos fields'
    | .cut pos producer consumer => do
      -- Direct IR passthrough (for testing)
      let prodP ← translateExpr producer
      let consP ← translateExpr consumer
      -- Wrap in mu to produce a Producer
      let α ← freshCovar
      return .mu pos α (.cut dummyPos prodP (.muTilde dummyPos "_" (.cut dummyPos consP (.covar dummyPos α))))
    | .mu pos name body => do
      -- Direct mu passthrough
      let bodyP ← translateExpr body
      return .mu pos name (.cut dummyPos bodyP (.covar dummyPos name))
    | .hash pos => do
      throw $ .notImplemented pos "hash self-reference"
    | .label pos name body => do
      -- ⟦label α {t}⟧ = μα.⟨⟦t⟧ | α⟩
      let bodyP ← withLabel name (translateExpr body)
      return .mu pos name (.cut dummyPos bodyP (.covar dummyPos name))
    | .goto pos value labelName => do
      -- ⟦goto(t; α)⟧ = μβ.⟨⟦t⟧ | α⟩ (β fresh, discarded)
      -- Check that label is in scope (static scoping)
      let inScope ← isLabelInScope labelName
      if !inScope then
        throw $ .undefinedLabel pos labelName
      let β ← freshCovar
      let valueP ← translateExpr value
      return .mu pos β (.cut dummyPos valueP (.covar dummyPos labelName))
end

-- Run translation
def translate (e : Expr) : Except TranslateError Producer :=
  match (translateExpr e).run {} with
  | .ok (p, _) => .ok p
  | .error e => .error e

-- Translate to Statement (wrapping producer with top-level continuation)
def translateToStatement (e : Expr) : Except TranslateError Statement := do
  let p ← translate e
  -- Return the producer connected to top-level continuation "halt"
  return .cut dummyPos p (.covar dummyPos "halt")

end Ziku.Translate
