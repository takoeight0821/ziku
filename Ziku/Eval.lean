import Ziku.Syntax

namespace Ziku

/-!
# Expression Evaluator

This module provides a simple evaluator for Ziku expressions.
Currently only supports arithmetic operations on integers.
-/

-- Simplified value type (no closures for now)
inductive Value where
  | int : Int → Value
  | bool : Bool → Value
  | unit : Value
  | string : String → Value
  | char : Char → Value
  deriving Repr, BEq

-- Environment mapping variables to values
abbrev Env := List (Ident × Value)

-- Helper to get int from value
def Value.toInt? : Value → Option Int
  | .int n => some n
  | _ => none

-- Helper to get bool from value
def Value.toBool? : Value → Option Bool
  | .bool b => some b
  | _ => none

-- Evaluate binary operation
def evalBinOp (op : BinOp) (v1 v2 : Value) : Option Value :=
  match op with
  | .add => match v1.toInt?, v2.toInt? with
    | some n1, some n2 => some (.int (n1 + n2))
    | _, _ => none
  | .sub => match v1.toInt?, v2.toInt? with
    | some n1, some n2 => some (.int (n1 - n2))
    | _, _ => none
  | .mul => match v1.toInt?, v2.toInt? with
    | some n1, some n2 => some (.int (n1 * n2))
    | _, _ => none
  | .div => match v1.toInt?, v2.toInt? with
    | some n1, some n2 =>
      if n2 == 0 then none else some (.int (n1 / n2))
    | _, _ => none
  | .eq => match v1.toInt?, v2.toInt? with
    | some n1, some n2 => some (.bool (n1 == n2))
    | _, _ => none
  | .ne => match v1.toInt?, v2.toInt? with
    | some n1, some n2 => some (.bool (n1 != n2))
    | _, _ => none
  | .lt => match v1.toInt?, v2.toInt? with
    | some n1, some n2 => some (.bool (n1 < n2))
    | _, _ => none
  | .le => match v1.toInt?, v2.toInt? with
    | some n1, some n2 => some (.bool (n1 <= n2))
    | _, _ => none
  | .gt => match v1.toInt?, v2.toInt? with
    | some n1, some n2 => some (.bool (n1 > n2))
    | _, _ => none
  | .ge => match v1.toInt?, v2.toInt? with
    | some n1, some n2 => some (.bool (n1 >= n2))
    | _, _ => none
  | .and => match v1.toBool?, v2.toBool? with
    | some b1, some b2 => some (.bool (b1 && b2))
    | _, _ => none
  | .or => match v1.toBool?, v2.toBool? with
    | some b1, some b2 => some (.bool (b1 || b2))
    | _, _ => none
  | .concat => none  -- String concat not yet implemented
  | .pipe => none    -- Pipe operator needs special evaluation

-- Evaluate unary operation
def evalUnaryOp (op : UnaryOp) (v : Value) : Option Value :=
  match op with
  | .neg => match v.toInt? with
    | some n => some (.int (-n))
    | none => none
  | .not => match v.toBool? with
    | some b => some (.bool (!b))
    | none => none

-- Simple evaluator (handles basic arithmetic expressions)
-- Note: Lambdas and application not yet supported in this simplified version
partial def eval (env : Env) : Expr → Option Value
  | .lit (.int n) => some (.int n)
  | .lit (.bool b) => some (.bool b)
  | .lit .unit => some .unit
  | .lit (.string s) => some (.string s)
  | .lit (.char c) => some (.char c)
  | .lit (.float _) => none  -- Float not yet supported
  | .var x => env.lookup x
  | .hash => none  -- Self-reference needs special handling
  | .binOp op e1 e2 =>
    match eval env e1, eval env e2 with
    | some v1, some v2 => evalBinOp op v1 v2
    | _, _ => none
  | .unaryOp op e =>
    match eval env e with
    | some v => evalUnaryOp op v
    | none => none
  | .lam _ _ => none  -- Lambdas not yet supported
  | .app _ _ => none  -- Application not yet supported
  | .let_ x _ e1 e2 =>
    match eval env e1 with
    | some v => eval ((x, v) :: env) e2
    | none => none
  | .letRec _ _ _ _ => none  -- Recursive let not yet supported
  | .if_ cond thenBranch elseBranch =>
    match eval env cond with
    | some (.bool true) => eval env thenBranch
    | some (.bool false) => eval env elseBranch
    | _ => none
  | .match_ _ _ => none  -- Pattern matching not yet implemented
  | .codata _ => none    -- Codata blocks not yet implemented
  | .field _ _ => none   -- Field access not yet implemented
  | .ann e _ => eval env e
  | .record _ => none    -- Records not yet implemented
  | .cut _ _ => none     -- Sequent cut not yet implemented
  | .mu _ _ => none      -- Mu abstraction not yet implemented

-- Pretty print value
def Value.toString : Value → String
  | .int n => s!"{n}"
  | .bool b => if b then "true" else "false"
  | .unit => "()"
  | .string s => s!"\"{s}\""
  | .char c => s!"'{c}'"

instance : ToString Value := ⟨Value.toString⟩

end Ziku
