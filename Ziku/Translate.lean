import Ziku.Syntax
import Ziku.IR.Syntax
import Ziku.IR.Eval
import Ziku.IR.Focusing

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

-- Inhabited instances for partial functions
instance : Inhabited (TranslateM Producer) where
  default := throw (.notImplemented { line := 0, col := 0 } "uninhabited")

instance : Inhabited (TranslateM Statement) where
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

/-!
## Pattern Compilation

Nested patterns are compiled to nested case expressions using join points for failure handling.

Example:
```
match x { | Cons(MNum(a), rest) => body1 | _ => fallback }
```
becomes:
```
mu result.
  mu fail1.
    <x | case { Cons(tmp1, rest) => <tmp1 | case { MNum(a) => <body1 | result>, _wild => <() | fail1> }>, _wild => <() | fail1> }>
  <fallback | result>
```
-/

-- Convert literal to pseudo-constructor name for pattern matching
def litToConName : Lit → Ident
  | .int n => s!"_lit_int_{n}"
  | .bool b => s!"_lit_bool_{b}"
  | .string s => s!"_lit_string_{s}"
  | .char c => s!"_lit_rune_{c.val}"
  | .float f => s!"_lit_float_{f}"
  | .unit => "_lit_unit"

-- Generate fresh variable name
def freshVar : TranslateM Ident := do
  let s ← get
  let name := s!"_tmp{s.freshCounter}"
  set { s with freshCounter := s.freshCounter + 1 }
  return name

-- Describes what to do with a constructor argument pattern
inductive ArgPattern where
  | bindVar : Ident → ArgPattern           -- Just bind to this variable
  | matchNested : Pat → Ident → ArgPattern -- Match nested pattern against temp var
  | checkLit : Lit → Ident → ArgPattern    -- Check literal equality on temp var
  deriving Repr

-- Analyze a pattern argument to determine how to handle it
def analyzePatternArg (pat : Pat) : TranslateM ArgPattern :=
  match pat with
  | .var _ x => return .bindVar x
  | .wild _ => do
    let tmp ← freshVar
    return .bindVar tmp
  | .paren _ p => analyzePatternArg p
  | .ann _ p _ => analyzePatternArg p
  | .con _ _ _ => do
    let tmp ← freshVar
    return .matchNested pat tmp
  | .lit _ l => do
    let tmp ← freshVar
    return .checkLit l tmp

-- Get the variable name to bind for an ArgPattern
def argPatternVar : ArgPattern → Ident
  | .bindVar x => x
  | .matchNested _ tmp => tmp
  | .checkLit _ tmp => tmp

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
      -- Pattern compilation with nested pattern support
      -- Uses compileCases which handles nested patterns via join points
      let α ← freshCovar
      let scrutineeP ← translateExpr scrutinee
      let matchStmt ← compileCases pos scrutineeP cases α
      return .mu pos α matchStmt
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

  -- Compile nested patterns for constructor arguments
  -- Takes list of ArgPatterns and generates nested case expressions
  partial def compileArgPatterns
      (pos : SourcePos)
      (argPatterns : List ArgPattern)
      (success : TranslateM Statement)  -- What to do on success
      (failLabel : Ident)               -- Where to jump on failure
      : TranslateM Statement := do
    match argPatterns with
    | [] => success
    | ap :: rest =>
      let restCompile := compileArgPatterns pos rest success failLabel
      match ap with
      | .bindVar _ => restCompile  -- Already bound by outer case
      | .matchNested pat tmp => do
        -- Generate nested case for this argument
        compilePattern pos (.var pos tmp) pat restCompile failLabel
      | .checkLit l tmp => do
        -- Generate literal equality check
        let restBody ← restCompile
        let litConName := litToConName l
        let failStmt := Statement.cut pos (.lit pos .unit) (.covar pos failLabel)
        return .cut pos (.var pos tmp) (.case pos [
          (litConName, [], restBody),
          ("_wild", [], failStmt)
        ])

  -- Compile a pattern against a scrutinee with success/failure continuations
  -- success: what to generate when pattern matches
  -- failLabel: label to jump to when pattern fails
  partial def compilePattern
      (pos : SourcePos)
      (scrutinee : Producer)
      (pat : Pat)
      (success : TranslateM Statement)
      (failLabel : Ident)
      : TranslateM Statement := do
    match pat with
    | .var _ x => do
      -- Variable always matches, bind and continue
      let body ← success
      return .cut pos scrutinee (.muTilde pos x body)
    | .wild _ => do
      -- Wildcard always matches, just continue
      success
    | .lit _ l => do
      -- Generate case with literal branch and wildcard to failure
      let successBody ← success
      let litConName := litToConName l
      let failStmt := Statement.cut pos (.lit pos .unit) (.covar pos failLabel)
      return .cut pos scrutinee (.case pos [
        (litConName, [], successBody),
        ("_wild", [], failStmt)
      ])
    | .con _ conName args => do
      -- Analyze each argument pattern
      let argPatterns ← args.mapM analyzePatternArg
      let vars := argPatterns.map argPatternVar

      -- Generate nested matches for arguments that need it
      let nestedSuccess := compileArgPatterns pos argPatterns success failLabel

      -- Generate the outer case with constructor and wildcard
      let successBody ← nestedSuccess
      let failStmt := Statement.cut pos (.lit pos .unit) (.covar pos failLabel)
      return .cut pos scrutinee (.case pos [
        (conName, vars, successBody),
        ("_wild", [], failStmt)
      ])
    | .paren _ p => compilePattern pos scrutinee p success failLabel
    | .ann _ p _ => compilePattern pos scrutinee p success failLabel

  -- Compile a list of pattern match cases with failure fallthrough
  -- Each branch is wrapped in mu failLabel. so failures jump to next branch
  partial def compileCases
      (pos : SourcePos)
      (scrutinee : Producer)
      (cases : List (Pat × Expr))
      (resultCont : Ident)  -- The final result continuation
      : TranslateM Statement := do
    match cases with
    | [] =>
      -- No more cases - this shouldn't happen in well-formed code
      -- Return unit to indicate match failure (could be improved with error)
      return .cut pos (.lit pos .unit) (.covar pos resultCont)
    | [(pat, body)] => do
      -- Last case - use a dummy fail label (match should be exhaustive)
      let failLabel ← freshCovar
      let bodyP ← translateExpr body
      let bodyStmt := Statement.cut pos bodyP (.covar pos resultCont)
      -- For last branch, failure just returns unit (non-exhaustive match)
      let failBody := Statement.cut pos (.lit pos .unit) (.covar pos resultCont)
      let patternStmt ← compilePattern pos scrutinee pat (pure bodyStmt) failLabel
      return .cut pos (.mu pos failLabel patternStmt) (.muTilde pos "_" failBody)
    | (pat, body) :: rest => do
      -- Generate: mu failLabel. <pattern match> where fail jumps to next branch
      let failLabel ← freshCovar
      let bodyP ← translateExpr body
      let bodyStmt := Statement.cut pos bodyP (.covar pos resultCont)
      let patternStmt ← compilePattern pos scrutinee pat (pure bodyStmt) failLabel
      -- After fail: try remaining cases
      let restStmt ← compileCases pos scrutinee rest resultCont
      return .cut pos (.mu pos failLabel patternStmt) (.muTilde pos "_" restStmt)
end

-- Run translation
def translate (e : Expr) : Except TranslateError Producer :=
  match (translateExpr e).run {} with
  | .ok (p, _) => .ok p
  | .error e => .error e

-- Translate to Statement (wrapping producer with top-level continuation)
-- Applies static focusing transformation to ensure all non-values are lifted
def translateToStatement (e : Expr) : Except TranslateError Statement := do
  let p ← translate e
  -- Return the producer connected to top-level continuation "halt"
  -- Use the producer's position for the generated cut and covar
  let unfocused := Statement.cut p.pos p (.covar p.pos "halt")
  -- Apply focusing transformation to ensure proper evaluation order
  return IR.Focusing.focus unfocused

end Ziku.Translate
