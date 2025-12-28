import Ziku.Syntax
import Ziku.Elaborate

namespace Ziku

/-!
# Expression Evaluator

This module provides a simple evaluator for Ziku expressions.
Currently only supports arithmetic operations on integers.
-/

-- Value type with closures and lazy record fields
inductive Value where
  | int : Int → Value
  | bool : Bool → Value
  | unit : Value
  | string : String → Value
  | char : Char → Value
  | closure : List (Ident × Value) → Ident → Expr → Value  -- Closure for lambdas (env inlined)
  | thunk : List (Ident × Value) → Expr → Value             -- Unevaluated expression (for lazy fields, env inlined)
  | record : List (Ident × Value) → Value  -- Record with lazy fields (thunks)
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

-- Simple evaluator (handles basic arithmetic expressions, lambdas, records)
partial def eval (env : Env) : Expr → Option Value
  | .lit _ (.int n) => some (.int n)
  | .lit _ (.bool b) => some (.bool b)
  | .lit _ .unit => some .unit
  | .lit _ (.string s) => some (.string s)
  | .lit _ (.char c) => some (.char c)
  | .lit _ (.float _) => none  -- Float not yet supported
  | .var _ x => env.lookup x
  | .binOp _ op e1 e2 =>
    match eval env e1, eval env e2 with
    | some v1, some v2 => evalBinOp op v1 v2
    | _, _ => none
  | .unaryOp _ op e =>
    match eval env e with
    | some v => evalUnaryOp op v
    | none => none
  | .lam _pos param body => some (.closure env param body)
  | .app _ fn arg => do
    let fnVal ← eval env fn
    -- Force evaluation of thunks
    let fnVal ← match fnVal with
      | .thunk tenv te => eval tenv te
      | v => some v
    match fnVal with
    | .closure closureEnv param body =>
      let argVal ← eval env arg
      eval ((param, argVal) :: closureEnv) body
    | _ => none
  | .let_ _ x _ e1 e2 =>
    match eval env e1 with
    | some v => eval ((x, v) :: env) e2
    | none => none
  | .letRec _ _ _ _ _ => none  -- Recursive let not yet supported
  | .if_ _ cond thenBranch elseBranch =>
    match eval env cond with
    | some (.bool true) => eval env thenBranch
    | some (.bool false) => eval env elseBranch
    | _ => none
  | .match_ _ _ _ => none  -- Pattern matching not yet implemented
  | .codata pos clauses =>
    -- Elaborate codata to record/lambda before evaluation
    match elaborate pos clauses with
    | .ok elaborated => eval env elaborated
    | .error _ => none
  | .field _ e fieldName => do
    let recVal ← eval env e
    -- Force evaluation of thunks
    let recVal ← match recVal with
      | .thunk tenv te => eval tenv te
      | v => some v
    match recVal with
    | .record fields =>
      -- Lookup field and force it (lazy evaluation)
      match fields.lookup fieldName with
      | some fieldVal =>
        -- Force the field value (lazy evaluation)
        match fieldVal with
        | .thunk fenv fe => eval fenv fe
        | v => some v
      | none => none
    | _ => none
  | .ann _ e _ => eval env e
  | .record _ fields =>
    -- Wrap each field value in a thunk for lazy evaluation
    let lazyFields := fields.map (fun (name, expr) => (name, .thunk env expr))
    some (.record lazyFields)
  | .cut _ _ _ => none     -- Sequent cut not yet implemented
  | .mu _ _ _ => none      -- Mu abstraction not yet implemented
  | .hash _ => none        -- Hash self-reference (should be substituted during elaboration)
  | .label _ _ _ => none   -- Label not yet implemented (requires continuation support)
  | .goto _ _ _ => none    -- Goto not yet implemented (requires continuation support)

-- Pretty print value
def Value.toString : Value → String
  | .int n => s!"{n}"
  | .bool b => if b then "true" else "false"
  | .unit => "()"
  | .string s => s!"\"{s}\""
  | .char c => s!"'{c}'"
  | .closure _ _ _ => "<closure>"
  | .thunk _ _ => "<thunk>"
  | .record fields =>
    let fs := fields.map (fun (n, _) => s!"{n} = <lazy>")
    "{ " ++ String.intercalate ", " fs ++ " }"

instance : ToString Value := ⟨Value.toString⟩

end Ziku
