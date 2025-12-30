import Ziku.Syntax
import Ziku.IR.Syntax

namespace Ziku.IR

/-!
# Sequent Calculus IR Evaluator

Implements evaluation for the λμμ̃-calculus IR based on "Grokking the Sequent Calculus" (ICFP 2024).

## Reduction Rules

```
⟨μα.s | c̄⟩    ⊲  s[c̄/α]     (μ-reduction)
⟨v̄ | μ̃x.s⟩    ⊲  s[v̄/x]     (μ̃-reduction, v is value)
```

The key insight is that:
- μα.s captures the current continuation α and continues with s
- μ̃x.s binds the incoming value x and continues with s
- ⟨p | c⟩ connects a producer p with consumer c
-/

open Ziku (SourcePos Ident BinOp Lit)

-- Values in IR are producers that need no further computation
-- Note: mu is NOT a value because μα.s needs to be paired with a consumer
partial def Producer.isValue : Producer → Bool
  | .var _ _ => true      -- Variables are values (already bound)
  | .lit _ _ => true      -- Literals are values
  | .mu _ _ _ => false    -- mu needs to be paired with consumer
  | .cocase _ _ => true   -- cocase is a value (like a closure)
  | .record _ _ => true   -- record is a value

-- Substitution: replace variable x with producer p in statement
mutual
partial def Producer.substVar (x : Ident) (p : Producer) : Producer → Producer
  | .var pos y => if y == x then p else .var pos y
  | .lit pos l => .lit pos l
  | .mu pos α s =>
    -- α is a covariable, doesn't shadow x
    .mu pos α (Statement.substVar x p s)
  | .cocase pos branches =>
    .cocase pos (branches.map fun (d, vars, s) =>
      if vars.contains x then (d, vars, s)  -- x is shadowed
      else (d, vars, Statement.substVar x p s))
  | .record pos fields =>
    .record pos (fields.map fun (n, prod) => (n, Producer.substVar x p prod))

partial def Consumer.substVar (x : Ident) (p : Producer) : Consumer → Consumer
  | .covar pos α => .covar pos α
  | .muTilde pos y s =>
    if y == x then .muTilde pos y s  -- x is shadowed
    else .muTilde pos y (Statement.substVar x p s)
  | .case pos branches =>
    .case pos (branches.map fun (k, vars, s) =>
      if vars.contains x then (k, vars, s)  -- x is shadowed
      else (k, vars, Statement.substVar x p s))
  | .destructor pos d ps c =>
    .destructor pos d (ps.map (Producer.substVar x p)) (Consumer.substVar x p c)

partial def Statement.substVar (x : Ident) (p : Producer) : Statement → Statement
  | .cut pos prod cons => .cut pos (Producer.substVar x p prod) (Consumer.substVar x p cons)
  | .binOp pos op p1 p2 c => .binOp pos op (Producer.substVar x p p1) (Producer.substVar x p p2) (Consumer.substVar x p c)
  | .ifz pos cond s1 s2 => .ifz pos (Producer.substVar x p cond) (Statement.substVar x p s1) (Statement.substVar x p s2)
  | .call pos f ps cs => .call pos f (ps.map (Producer.substVar x p)) (cs.map (Consumer.substVar x p))
end

-- Substitution: replace covariable α with consumer c in statement
mutual
partial def Producer.substCovar (α : Ident) (c : Consumer) : Producer → Producer
  | .var pos x => .var pos x
  | .lit pos l => .lit pos l
  | .mu pos β s =>
    if β == α then .mu pos β s  -- α is shadowed
    else .mu pos β (Statement.substCovar α c s)
  | .cocase pos branches =>
    .cocase pos (branches.map fun (d, vars, s) =>
      if vars.contains α then (d, vars, s)  -- α is shadowed (if in covar position)
      else (d, vars, Statement.substCovar α c s))
  | .record pos fields =>
    .record pos (fields.map fun (n, prod) => (n, Producer.substCovar α c prod))

partial def Consumer.substCovar (α : Ident) (c : Consumer) : Consumer → Consumer
  | .covar pos β => if β == α then c else .covar pos β
  | .muTilde pos x s =>
    -- x is a variable, doesn't shadow α
    .muTilde pos x (Statement.substCovar α c s)
  | .case pos branches =>
    .case pos (branches.map fun (k, vars, s) =>
      if vars.contains α then (k, vars, s)  -- α is shadowed
      else (k, vars, Statement.substCovar α c s))
  | .destructor pos d ps c' =>
    .destructor pos d (ps.map (Producer.substCovar α c)) (Consumer.substCovar α c c')

partial def Statement.substCovar (α : Ident) (c : Consumer) : Statement → Statement
  | .cut pos prod cons => .cut pos (Producer.substCovar α c prod) (Consumer.substCovar α c cons)
  | .binOp pos op p1 p2 cons => .binOp pos op (Producer.substCovar α c p1) (Producer.substCovar α c p2) (Consumer.substCovar α c cons)
  | .ifz pos cond s1 s2 => .ifz pos (Producer.substCovar α c cond) (Statement.substCovar α c s1) (Statement.substCovar α c s2)
  | .call pos f ps cs => .call pos f (ps.map (Producer.substCovar α c)) (cs.map (Consumer.substCovar α c))
end

-- Evaluation result
inductive EvalResult where
  | value : Producer → EvalResult      -- Evaluation completed with a value
  | stuck : Statement → EvalResult     -- Evaluation got stuck
  | error : String → EvalResult        -- Evaluation error
  deriving Repr, Inhabited

-- Helper: evaluate binary operation
def evalBinOp (op : BinOp) (p1 p2 : Producer) : Option Producer :=
  match p1, p2 with
  | .lit pos (.int n1), .lit _ (.int n2) =>
    match op with
    | .add => some (.lit pos (.int (n1 + n2)))
    | .sub => some (.lit pos (.int (n1 - n2)))
    | .mul => some (.lit pos (.int (n1 * n2)))
    | .div => if n2 == 0 then none else some (.lit pos (.int (n1 / n2)))
    | .eq => some (.lit pos (.bool (n1 == n2)))
    | .ne => some (.lit pos (.bool (n1 != n2)))
    | .lt => some (.lit pos (.bool (n1 < n2)))
    | .le => some (.lit pos (.bool (n1 <= n2)))
    | .gt => some (.lit pos (.bool (n1 > n2)))
    | .ge => some (.lit pos (.bool (n1 >= n2)))
    | _ => none
  | .lit pos (.bool b1), .lit _ (.bool b2) =>
    match op with
    | .and => some (.lit pos (.bool (b1 && b2)))
    | .or => some (.lit pos (.bool (b1 || b2)))
    | _ => none
  | _, _ => none

-- Step-based evaluation (small-step semantics)
-- Returns None if no reduction is possible (stuck or value)
partial def step : Statement → Option Statement
  | .cut pos p c =>
    match p, c with
    -- μ-reduction: ⟨μα.s | c̄⟩ ⊲ s[c̄/α]
    | .mu _ α s, _ => some (s.substCovar α c)
    -- μ̃-reduction: ⟨v̄ | μ̃x.s⟩ ⊲ s[v'/x] where v' is p with enough self-substitution for recursion
    | _, .muTilde _ x s =>
      if p.isValue then
        -- Tie the knot: iterate substitution to handle recursive references
        -- Each iteration unfolds one more level of recursion
        -- Need 10+ iterations for nested lambda + codata (like Fibonacci streams)
        let p1 := p.substVar x p
        let p2 := p1.substVar x p1
        let p3 := p2.substVar x p2
        let p4 := p3.substVar x p3
        let p5 := p4.substVar x p4
        let p6 := p5.substVar x p5
        let p7 := p6.substVar x p6
        let p8 := p7.substVar x p7
        let p9 := p8.substVar x p8
        let p10 := p9.substVar x p9
        some (s.substVar x p10)
      else none
    -- Destructor application: ⟨cocase {...} | D(p̄; c)⟩
    -- vars = [arg1, ..., argN, continuation_covar]
    -- args = [p1, ..., pN]
    -- cont = continuation consumer
    | .cocase _ branches, .destructor _ d args cont =>
      match branches.find? (fun (d', _, _) => d' == d) with
      | some (_, vars, body) =>
        -- Arity check: vars should have one more element than args (the continuation covar)
        if vars.length != args.length + 1 then none
        else
          match vars.getLast? with
          | none => none
          | some contCovar =>
            let argVars := vars.dropLast
            -- Substitute argument producers for argument variables
            let body' := argVars.zip args |>.foldl (fun s (x, p) => s.substVar x p) body
            -- Substitute continuation consumer for continuation covariable
            let body'' := body'.substCovar contCovar cont
            some body''
      | none => none
    -- Record field access: ⟨{ ... fᵢ = vᵢ ... } | fᵢ(; c)⟩ → ⟨vᵢ | c⟩
    | .record _ fields, .destructor pos fieldName [] cont =>
      match fields.find? (fun (f, _) => f == fieldName) with
      | some (_, value) => some (.cut pos value cont)
      | none => none
    | _, _ => none
  -- Binary operation: ⊙(p₁, p₂; c)
  | .binOp pos op p1 p2 c =>
    match p1, p2 with
    -- If first operand is μ, evaluate it first
    | .mu _ _ _, _ =>
      some (.cut pos p1 (.muTilde pos "_binop_l" (.binOp pos op (.var pos "_binop_l") p2 c)))
    -- If second operand is μ, evaluate it first
    | _, .mu _ _ _ =>
      some (.cut pos p2 (.muTilde pos "_binop_r" (.binOp pos op p1 (.var pos "_binop_r") c)))
    | _, _ =>
      match evalBinOp op p1 p2 with
      | some result => some (.cut pos result c)
      | none => none
  -- Conditional: ifz(p, s₁, s₂)
  | .ifz pos cond s1 s2 =>
    match cond with
    | .lit _ (.bool true) => some s1
    | .lit _ (.bool false) => some s2
    | .lit _ (.int n) => if n == 0 then some s1 else some s2
    -- When condition is a μ, we need to first evaluate it
    -- ifz(μα.s, s1, s2) → ⟨μα.s | μ̃x.ifz(x, s1, s2)⟩
    | .mu _ _ _ =>
      some (.cut pos cond (.muTilde pos "_ifz_cond" (.ifz pos (.var pos "_ifz_cond") s1 s2)))
    | _ => none
  -- Function call: handled externally
  | .call _ _ _ _ => none

-- Multi-step evaluation with fuel (to prevent infinite loops)
partial def evalWithFuel (fuel : Nat) (s : Statement) : EvalResult :=
  if fuel == 0 then
    .stuck s
  else
    match step s with
    | some s' => evalWithFuel (fuel - 1) s'
    | none =>
      -- Check if we're at a terminal state
      match s with
      | .cut _ p (.covar _ "halt") =>
        if p.isValue then .value p
        else .stuck s
      | _ => .stuck s

-- Default fuel for evaluation
def defaultFuel : Nat := 100000

-- Main evaluation function
def eval (s : Statement) : EvalResult :=
  evalWithFuel defaultFuel s

-- Helper function to build truncated record string incrementally
-- Truncation is based on VALUE length, not field name length
partial def buildRecordFields (remaining : List (Ident × Producer)) (acc : String)
    (pfx : String) (sfx : String) (dots : String) (maxLen : Nat) (maxValueLen : Nat) : String :=
  match remaining with
  | [] => acc ++ sfx
  | (name, value) :: rest =>
    let valueStr := value.toString
    let fieldStr := s!"{name} = {valueStr}"
    let separator := if acc == pfx then "" else ", "
    let newAcc := acc ++ separator ++ fieldStr
    -- Primary check: is the VALUE too long?
    if valueStr.length >= maxValueLen then
      -- Show field name but truncate value
      let truncatedField := s!"{name} = ..."
      acc ++ separator ++ truncatedField ++ ", ... }"
    -- Secondary check: would total exceed limit?
    else if newAcc.length + sfx.length > maxLen then
      -- If this is the first field and value is short, include it anyway
      -- (don't truncate just because field name is long)
      if acc == pfx then
        buildRecordFields rest newAcc pfx sfx dots maxLen maxValueLen
      else
        acc ++ dots
    else
      buildRecordFields rest newAcc pfx sfx dots maxLen maxValueLen

-- Truncate record display if too long (over maxLen characters)
-- maxValueLen determines when a single value is considered too long
partial def truncateRecord (p : Producer) (maxLen : Nat := 80) (maxValueLen : Nat := 40) : String :=
  match p with
  | .record _ fields =>
    if fields.isEmpty then "{ }"
    else
      let pfx := "{ "
      let sfx := " }"
      let dots := ", ... }"
      buildRecordFields fields pfx pfx sfx dots maxLen maxValueLen
  | _ => p.toString

-- Pretty print evaluation result
def EvalResult.toString : EvalResult → String
  | .value p => s!"Value: {truncateRecord p}"
  | .stuck s => s!"Stuck: {s}"
  | .error msg => s!"Error: {msg}"

instance : ToString EvalResult := ⟨EvalResult.toString⟩

end Ziku.IR
