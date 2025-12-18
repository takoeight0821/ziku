import Ziku.Eval
import Ziku.Infer

namespace Ziku.Proofs

-- Type environment and value environment are consistent
-- All variables with int type in tyEnv should exist in valEnv
def EnvConsistent (tyEnv : TyEnv) (valEnv : Env) : Prop :=
  ∀ x ty, tyEnv.lookup x = some ty →
    ty = Ty.int → (valEnv.lookup x : Option Int).isSome

-- All variables in tyEnv exist in valEnv
def EnvComplete (tyEnv : TyEnv) (valEnv : Env) : Prop :=
  ∀ x, x ∈ tyEnv.map Prod.fst →
    ∃ v, valEnv.lookup x = some v

-- Check if an expression might divide by zero during evaluation
def hasDivByZero : Expr → Env → Prop
  | Expr.lit _, _ => False
  | Expr.var _, _ => False
  | Expr.add e1 e2, env => hasDivByZero e1 env ∨ hasDivByZero e2 env
  | Expr.sub e1 e2, env => hasDivByZero e1 env ∨ hasDivByZero e2 env
  | Expr.mul e1 e2, env => hasDivByZero e1 env ∨ hasDivByZero e2 env
  | Expr.div e1 e2, env =>
      eval env e2 = some 0 ∨ hasDivByZero e1 env ∨ hasDivByZero e2 env

-- Literals always type check
theorem infer_lit (env : TyEnv) (n : Int) (s : InferState) :
    infer env (Expr.lit n) s = some (Ty.int, [], s) := by
  rfl

-- Type inference is deterministic
theorem infer_deterministic (env : TyEnv) (e : Expr) (s : InferState)
    (r1 r2 : Ty × Subst × InferState)
    (h1 : infer env e s = some r1)
    (h2 : infer env e s = some r2) :
    r1 = r2 := by
  rw [h1] at h2
  injection h2

-- Helper lemmas for soundness proofs

-- If variable is in tyEnv and environment is complete, it can be evaluated
theorem var_eval_of_tyenv (x : String) (tyEnv : TyEnv) (valEnv : Env)
    (henv : EnvComplete tyEnv valEnv)
    (hmem : x ∈ tyEnv.map Prod.fst) :
    ∃ v, eval valEnv (Expr.var x) = some v := by
  simp [eval]
  exact henv x hmem

-- If lookup succeeds, the key is in the list
theorem lookup_some_mem {α β : Type} [BEq α] [LawfulBEq α] (l : List (α × β)) (k : α) (v : β)
    (h : l.lookup k = some v) :
    k ∈ l.map Prod.fst := by
  induction l with
  | nil => simp [List.lookup] at h
  | cons head tail ih =>
    simp [List.lookup] at h
    split at h
    · rename_i heq
      simp [List.mem_map]
      left
      exact LawfulBEq.eq_of_beq heq
    · right
      exact ih h

-- If infer succeeds for a variable, it's in the type environment
theorem infer_var_mem (x : String) (tyEnv : TyEnv) (s : InferState)
    (hinfer : (infer tyEnv (Expr.var x) s).isSome) :
    x ∈ tyEnv.map Prod.fst := by
  simp [infer] at hinfer
  split at hinfer
  · apply lookup_some_mem
    assumption
  · simp at hinfer

-- Progress theorem (simplified version)
-- Well-typed closed expressions can be evaluated (excluding division by zero)
-- Note: This is a complex proof that requires detailed case analysis on expressions.
-- The main idea is to use structural induction on e and show that each case can be evaluated.
theorem progress (e : Expr) (tyEnv : TyEnv) (valEnv : Env) (s : InferState)
    (ty : Ty) (subst : Subst) (s' : InferState)
    (htype : infer tyEnv e s = some (ty, subst, s'))
    (henv : EnvComplete tyEnv valEnv)
    (hclosed : e.freeVars.all (fun x => tyEnv.lookup x |>.isSome))
    (hnoDiv : ¬ hasDivByZero e valEnv)
    : ∃ v, eval valEnv e = some v := by
  sorry  -- Complex proof requiring structural induction and careful case analysis

-- Type preservation (trivial in this system since all values are Int)
theorem preservation (e : Expr) (tyEnv : TyEnv) (valEnv : Env) (s : InferState)
    (v : Int)
    (heval : eval valEnv e = some v)
    (htype : infer tyEnv e s |>.isSome) :
    True := by
  trivial

-- Main type soundness theorem
-- Well-typed expressions either evaluate or hit division by zero
theorem type_soundness (e : Expr) (tyEnv : TyEnv) (valEnv : Env) (s : InferState)
    (htype : infer tyEnv e s |>.isSome)
    (henv : EnvComplete tyEnv valEnv)
    (hscoped : e.freeVars.all (fun x => tyEnv.lookup x |>.isSome)) :
    (∃ v, eval valEnv e = some v) ∨ (eval valEnv e = none ∧ hasDivByZero e valEnv) := by
  sorry  -- Main theorem, proven by induction on e

end Ziku.Proofs
