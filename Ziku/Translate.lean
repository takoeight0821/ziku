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

open Ziku (SourcePos Ident BinOp UnaryOp Builtin Lit Expr)
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

-- Get builtin enum from name
def nameToBuiltin : String → Option Builtin
  | "strLen"    => some .strLen
  | "strAt"     => some .strAt
  | "strSub"    => some .strSub
  | "strToInt"  => some .strToInt
  | "intToStr"  => some .intToStr
  | "runeToStr" => some .runeToStr
  | "intToRune" => some .intToRune
  | "runeToInt" => some .runeToInt
  | _           => none

-- Get arity of builtin function
def builtinArity : Builtin → Nat
  | .strLen    => 1
  | .strAt     => 2
  | .strSub    => 3
  | .strToInt  => 1
  | .intToStr  => 1
  | .runeToStr => 1
  | .intToRune => 1
  | .runeToInt => 1

-- Collect all curried arguments from a chain of applications
-- e.g., ((f x) y) z  =>  (f, [x, y, z])
def collectAppArgs : Expr → (Expr × List Expr)
  | .app _ fn arg =>
    let (base, args) := collectAppArgs fn
    (base, args ++ [arg])
  | e => (e, [])

-- Add label to scope
def withLabel (name : Ident) (m : TranslateM α) : TranslateM α := do
  let s ← get
  set { s with labelScope := name :: s.labelScope }
  let result ← m
  let s' ← get
  set { s' with labelScope := s.labelScope }
  return result

/-
Translation produces a Producer in most cases.
The key insight from Grokking is that surface expressions are producers,
and we use μ to capture the continuation context.
-/

open Ziku (Pat)

-- Extract constructor name and bound variables from a pattern
-- For nested patterns, we currently only support simple variable bindings
partial def patternToIRBranch (pat : Pat) : TranslateM (Ident × List Ident) :=
  match pat with
  | .con _ conName args => do
    -- Constructor pattern: extract variable names from arguments
    let vars ← args.mapM extractVarFromPat
    return (conName, vars)
  | .var _ x =>
    -- Variable pattern: catch-all, bind to "_var" pseudo-constructor
    return ("_var", [x])
  | .wild _ =>
    -- Wildcard: catch-all, bind to "_wild" pseudo-constructor
    return ("_wild", [])
  | .lit pos l =>
    -- Literal pattern: treat as nullary constructor
    let conName := match l with
      | .int n => s!"_lit_int_{n}"
      | .bool b => s!"_lit_bool_{b}"
      | .string s => s!"_lit_string_{s}"
      | _ => "_lit_other"
    return (conName, [])
  | .paren _ p => patternToIRBranch p
  | .ann _ p _ => patternToIRBranch p
where
  -- Extract variable name from a simple pattern (for constructor arguments)
  extractVarFromPat (pat : Pat) : TranslateM Ident :=
    match pat with
    | .var _ x => return x
    | .wild _ => do
      -- Generate fresh name for wildcard
      let s ← get
      let name := s!"_wild{s.freshCounter}"
      set { s with freshCounter := s.freshCounter + 1 }
      return name
    | .paren _ p => extractVarFromPat p
    | .ann _ p _ => extractVarFromPat p
    | .con pos _ _ => throw $ .notImplemented pos "nested constructor pattern"
    | .lit pos _ => throw $ .notImplemented pos "literal in constructor pattern"

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
      return .mu pos α (.binOp pos op p1 p2 (.covar pos α))
    | .unaryOp pos _op _e => do
      -- Translate unary as binary with dummy
      throw $ .notImplemented pos "unary operator translation"
    | .lam pos param body => do
      -- ⟦λx.t⟧ = cocase {ap(x; α) ⇒ ⟨⟦t⟧ | α⟩}
      let α ← freshCovar
      let bodyP ← translateExpr body
      return .cocase pos [("ap", [param, α], .cut pos bodyP (.covar pos α))]
    | .app pos fn arg => do
      -- Check if this is a saturated builtin call
      let (baseExpr, allArgs) := collectAppArgs e
      match baseExpr with
      | .var _ name =>
        -- Check if base is a builtin
        match nameToBuiltin name with
        | some builtin =>
          -- Check if arity matches
          if allArgs.length == builtinArity builtin then
            -- Saturated builtin call: translate to Statement.builtin
            let α ← freshCovar
            let argsP ← allArgs.mapM translateExpr
            return .mu pos α (.builtin pos builtin argsP (.covar pos α))
          else
            -- Partial application or wrong arity - normal function call
            let α ← freshCovar
            let fnP ← translateExpr fn
            let argP ← translateExpr arg
            return .mu pos α (.cut pos fnP (.destructor pos "ap" [argP] (.covar pos α)))
        | none =>
          -- Not a builtin - normal function application
          let α ← freshCovar
          let fnP ← translateExpr fn
          let argP ← translateExpr arg
          return .mu pos α (.cut pos fnP (.destructor pos "ap" [argP] (.covar pos α)))
      | _ =>
        -- Not a variable base - normal function application
        let α ← freshCovar
        let fnP ← translateExpr fn
        let argP ← translateExpr arg
        return .mu pos α (.cut pos fnP (.destructor pos "ap" [argP] (.covar pos α)))
    | .let_ pos x _ e1 e2 => do
      -- ⟦let x = t₁ in t₂⟧ = μα.⟨⟦t₁⟧ | μ̃x.⟨⟦t₂⟧ | α⟩⟩
      let α ← freshCovar
      let p1 ← translateExpr e1
      let p2 ← translateExpr e2
      return .mu pos α (.cut pos p1 (.muTilde pos x (.cut pos p2 (.covar pos α))))
    | .letRec pos x _ e1 e2 => do
      -- ⟦let rec x = e₁ in e₂⟧ = μα.⟨fix x. ⟦e₁⟧ | μ̃x.⟨⟦e₂⟧ | α⟩⟩
      -- Use fixpoint combinator for proper recursive semantics
      let α ← freshCovar
      let p1 ← translateExpr e1
      -- Wrap in fix to create proper self-reference with lazy unfolding
      let fixP := IR.Producer.fix pos x p1
      let p2 ← translateExpr e2
      return .mu pos α (.cut pos fixP (.muTilde pos x (.cut pos p2 (.covar pos α))))
    | .if_ pos cond thenE elseE => do
      -- ⟦if t₁ then t₂ else t₃⟧ = μα.ifz(⟦t₁⟧, ⟨⟦t₂⟧ | α⟩, ⟨⟦t₃⟧ | α⟩)
      let α ← freshCovar
      let condP ← translateExpr cond
      let thenP ← translateExpr thenE
      let elseP ← translateExpr elseE
      return .mu pos α (.ifz pos condP
        (.cut pos thenP (.covar pos α))
        (.cut pos elseP (.covar pos α)))
    | .match_ pos scrutinee cases => do
      -- ⟦match e with | K1(x1,...) => e1 | ... end⟧
      -- = μα.⟨⟦e⟧ | case { K1(x1,...) => ⟨⟦e1⟧ | α⟩, ... }⟩
      let α ← freshCovar
      let scrutineeP ← translateExpr scrutinee
      let branches ← cases.mapM fun (pat, body) => do
        let (conName, vars) ← patternToIRBranch pat
        let bodyP ← translateExpr body
        let branchStmt := Statement.cut pos bodyP (.covar pos α)
        return (conName, vars, branchStmt)
      let caseConsumer := Consumer.case pos branches
      return .mu pos α (.cut pos scrutineeP caseConsumer)
    | .codata pos _ => do
      throw $ .notImplemented pos "codata block"
    | .field pos e fieldName => do
      -- ⟦e.f⟧ = μα.⟨⟦e⟧ | f(; α)⟩
      let α ← freshCovar
      let prodE ← translateExpr e
      return .mu pos α (.cut pos prodE (.destructor pos fieldName [] (.covar pos α)))
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
      return .mu pos α (.cut pos prodP (.muTilde pos "_" (.cut pos consP (.covar pos α))))
    | .mu pos name body => do
      -- Direct mu passthrough
      let bodyP ← translateExpr body
      return .mu pos name (.cut pos bodyP (.covar pos name))
    | .hash pos => do
      throw $ .notImplemented pos "hash self-reference"
    | .label pos name body => do
      -- ⟦label α {t}⟧ = μα.⟨⟦t⟧ | α⟩
      let bodyP ← withLabel name (translateExpr body)
      return .mu pos name (.cut pos bodyP (.covar pos name))
    | .goto pos value labelName => do
      -- ⟦goto(t; α)⟧ = μβ.⟨⟦t⟧ | α⟩ (β fresh, discarded)
      -- Check that label is in scope (static scoping)
      let inScope ← isLabelInScope labelName
      if !inScope then
        throw $ .undefinedLabel pos labelName
      let β ← freshCovar
      let valueP ← translateExpr value
      return .mu pos β (.cut pos valueP (.covar pos labelName))
    | .con pos conName args => do
      -- ⟦Con(e1, ..., en)⟧ = dataCon Con (⟦e1⟧, ..., ⟦en⟧)
      let argsP ← args.mapM translateExpr
      return .dataCon pos conName argsP
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
  -- Use the producer's position for the generated cut and covar
  return .cut p.pos p (.covar p.pos "halt")

end Ziku.Translate
