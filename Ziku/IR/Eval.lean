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

open Ziku (SourcePos Ident BinOp Builtin Lit)

-- Values in IR are producers that need no further computation
-- Note: mu is NOT a value because μα.s needs to be paired with a consumer
partial def Producer.isValue : Producer → Bool
  | .var _ _ => true      -- Variables are values (already bound)
  | .lit _ _ => true      -- Literals are values
  | .mu _ _ _ => false    -- mu needs to be paired with consumer
  | .cocase _ _ => true   -- cocase is a value (like a closure)
  | .record _ _ => true   -- record is a value
  | .fix _ _ _ => true    -- fix is a value (lazy, unfolds when consumed)
  | .dataCon _ _ args => args.all Producer.isValue  -- dataCon is value when all args are values

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
  | .fix pos y body =>
    if y == x then .fix pos y body  -- x is shadowed by fix binder
    else .fix pos y (Producer.substVar x p body)
  | .dataCon pos con args =>
    .dataCon pos con (args.map (Producer.substVar x p))

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
  | .builtin pos b ps c => .builtin pos b (ps.map (Producer.substVar x p)) (Consumer.substVar x p c)
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
  | .fix pos y body =>
    -- y is a variable, doesn't shadow α (which is a covariable)
    .fix pos y (Producer.substCovar α c body)
  | .dataCon pos con args =>
    .dataCon pos con (args.map (Producer.substCovar α c))

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
  | .builtin pos b ps cons => .builtin pos b (ps.map (Producer.substCovar α c)) (Consumer.substCovar α c cons)
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
  | .lit pos (.string s1), .lit _ (.string s2) =>
    match op with
    | .concat => some (.lit pos (.string (s1 ++ s2)))
    | _ => none
  | _, _ => none

-- Helper: evaluate built-in function
def evalBuiltin (b : Builtin) (args : List Producer) : Option Producer :=
  let pos : SourcePos := { line := 0, col := 0 }
  match b, args with
  | .strLen, [.lit _ (.string s)] =>
    -- String length in characters (Unicode code points)
    some (.lit pos (.int s.length))
  | .strAt, [.lit _ (.string s), .lit _ (.int i)] =>
    -- Get character at index (0-based)
    if i < 0 then none
    else
      let idx := i.toNat
      match s.toList[idx]? with
      | some c => some (.lit pos (.char c))
      | none => none
  | .strSub, [.lit _ (.string s), .lit _ (.int start), .lit _ (.int len)] =>
    -- Substring: strSub(s, start, length)
    if start < 0 || len < 0 then none
    else
      let startIdx := start.toNat
      let lenVal := len.toNat
      if startIdx > s.length then none
      else
        let result := s.drop startIdx |>.take lenVal
        some (.lit pos (.string result))
  | .strToInt, [.lit _ (.string s)] =>
    -- Parse string as integer
    match s.toInt? with
    | some n => some (.lit pos (.int n))
    | none => none
  | .intToStr, [.lit _ (.int n)] =>
    some (.lit pos (.string (toString n)))
  | .runeToStr, [.lit _ (.char c)] =>
    some (.lit pos (.string (String.singleton c)))
  | .intToRune, [.lit _ (.int n)] =>
    -- Convert integer to rune (Unicode code point)
    if n < 0 || n > 0x10FFFF then none
    else some (.lit pos (.char (Char.ofNat n.toNat)))
  | .runeToInt, [.lit _ (.char c)] =>
    some (.lit pos (.int c.toNat))
  | _, _ => none

-- Step-based evaluation (small-step semantics)
-- Returns None if no reduction is possible (stuck or value)
partial def step : Statement → Option Statement
  | .cut pos p c =>
    match p, c with
    -- μ-reduction: ⟨μα.s | c̄⟩ ⊲ s[c̄/α]
    | .mu _ α s, _ => some (s.substCovar α c)
    -- fix-reduction: ⟨fix x. p | c⟩ ⊲ ⟨p[fix x. p / x] | c⟩
    -- Lazy unfolding: fixpoint only unfolds when consumed
    | .fix fixPos x body, _ =>
      let fixProducer := Producer.fix fixPos x body
      let unfolded := Producer.substVar x fixProducer body
      some (.cut pos unfolded c)
    -- μ̃-reduction: ⟨v̄ | μ̃x.s⟩ ⊲ s[v̄/x] (v is value)
    | _, .muTilde _ x s =>
      if p.isValue then some (s.substVar x p)
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
    -- Data constructor + case: ⟨K(v1,...,vn) | case { K(x1,...,xn) => s, ... }⟩ ⊲ s[v1/x1,...,vn/xn]
    | .dataCon _ conName args, .case _ branches =>
      match branches.find? (fun (k, _, _) => k == conName) with
      | some (_, vars, body) =>
        if vars.length != args.length then none
        else
          let body' := vars.zip args |>.foldl (fun s (x, v) => s.substVar x v) body
          some body'
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
  -- Built-in function: builtin(p̄; c)
  | .builtin pos b ps c =>
    -- Find first non-value argument and evaluate it
    match ps.findIdx? (fun p => !p.isValue) with
    | some idx =>
      match ps[idx]? with
      | some (.mu muPos α s) =>
        -- Evaluate this argument first
        let freshName := s!"_builtin_arg{idx}"
        let ps' := ps.set idx (.var pos freshName)
        some (.cut pos (.mu muPos α s) (.muTilde pos freshName (.builtin pos b ps' c)))
      | _ => none
    | none =>
      -- All arguments are values, evaluate the builtin
      match evalBuiltin b ps with
      | some result => some (.cut pos result c)
      | none => none

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

-- Generic string truncation function
-- Truncates any string to specified maximum length
def truncate (s : String) (maxLen : Nat := 80) : String :=
  if s.length <= maxLen then s
  else if maxLen < 3 then "..."
  else s.take (maxLen - 3) ++ "..."

-- Pretty print evaluation result
def EvalResult.toString : EvalResult → String
  | .value p => s!"Value: {truncate p.toString}"
  | .stuck s => s!"Stuck: {s}"
  | .error msg => s!"Error: {msg}"

instance : ToString EvalResult := ⟨EvalResult.toString⟩

end Ziku.IR
