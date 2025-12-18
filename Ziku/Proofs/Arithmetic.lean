import Ziku.Eval

namespace Ziku.Proofs

-- Addition is commutative (semantic level)
theorem eval_add_comm (env : Env) (e1 e2 : Expr) :
    eval env (Expr.add e1 e2) = eval env (Expr.add e2 e1) := by
  simp only [eval]
  cases h1 : eval env e1 <;> cases h2 : eval env e2 <;> simp
  omega

-- Multiplication is commutative
theorem eval_mul_comm (env : Env) (e1 e2 : Expr) :
    eval env (Expr.mul e1 e2) = eval env (Expr.mul e2 e1) := by
  simp only [eval]
  cases h1 : eval env e1 <;> cases h2 : eval env e2 <;> simp
  rw [Int.mul_comm]

-- Addition is associative
theorem eval_add_assoc (env : Env) (e1 e2 e3 : Expr) :
    eval env (Expr.add (Expr.add e1 e2) e3) =
    eval env (Expr.add e1 (Expr.add e2 e3)) := by
  simp only [eval]
  cases h1 : eval env e1 <;> cases h2 : eval env e2 <;> cases h3 : eval env e3 <;> simp
  omega

-- Multiplication is associative
theorem eval_mul_assoc (env : Env) (e1 e2 e3 : Expr) :
    eval env (Expr.mul (Expr.mul e1 e2) e3) =
    eval env (Expr.mul e1 (Expr.mul e2 e3)) := by
  simp only [eval]
  cases h1 : eval env e1 <;> cases h2 : eval env e2 <;> cases h3 : eval env e3 <;> simp
  rw [Int.mul_assoc]

-- Distributivity: a * (b + c) = a * b + a * c
theorem eval_mul_add_distrib (env : Env) (e1 e2 e3 : Expr) :
    eval env (Expr.mul e1 (Expr.add e2 e3)) =
    eval env (Expr.add (Expr.mul e1 e2) (Expr.mul e1 e3)) := by
  simp only [eval]
  cases h1 : eval env e1 <;> cases h2 : eval env e2 <;> cases h3 : eval env e3 <;> simp
  rw [Int.mul_add]

end Ziku.Proofs
