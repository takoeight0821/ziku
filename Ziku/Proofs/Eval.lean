import Ziku.Eval

namespace Ziku.Proofs

-- Literal always evaluates successfully
theorem eval_lit (env : Env) (n : Int) :
    eval env (Expr.lit n) = some n := by
  rfl

-- Variable evaluation depends on environment
theorem eval_var_found (env : Env) (x : String) (v : Int)
    (h : env.lookup x = some v) :
    eval env (Expr.var x) = some v := by
  simp [eval, h]

theorem eval_var_not_found (env : Env) (x : String)
    (h : env.lookup x = none) :
    eval env (Expr.var x) = none := by
  simp [eval, h]

-- Division by zero returns none
theorem eval_div_zero (env : Env) (e1 e2 : Expr) (v1 : Int)
    (h1 : eval env e1 = some v1)
    (h2 : eval env e2 = some 0) :
    eval env (Expr.div e1 e2) = none := by
  simp [eval, h1, h2]

-- Addition evaluation
theorem eval_add (env : Env) (e1 e2 : Expr) (v1 v2 : Int)
    (h1 : eval env e1 = some v1)
    (h2 : eval env e2 = some v2) :
    eval env (Expr.add e1 e2) = some (v1 + v2) := by
  simp [eval, h1, h2]

-- Subtraction evaluation
theorem eval_sub (env : Env) (e1 e2 : Expr) (v1 v2 : Int)
    (h1 : eval env e1 = some v1)
    (h2 : eval env e2 = some v2) :
    eval env (Expr.sub e1 e2) = some (v1 - v2) := by
  simp [eval, h1, h2]

-- Multiplication evaluation
theorem eval_mul (env : Env) (e1 e2 : Expr) (v1 v2 : Int)
    (h1 : eval env e1 = some v1)
    (h2 : eval env e2 = some v2) :
    eval env (Expr.mul e1 e2) = some (v1 * v2) := by
  simp [eval, h1, h2]

-- Division by non-zero (simplified version)
-- Note: The full proof requires dealing with BEq vs Eq for Int
theorem eval_div_nonzero (env : Env) (e1 e2 : Expr) (v1 v2 : Int)
    (h1 : eval env e1 = some v1)
    (h2 : eval env e2 = some v2)
    (hnz : v2 ≠ 0) :
    eval env (Expr.div e1 e2) = some (v1 / v2) := by
  simp [eval, h1, h2]
  exact hnz

end Ziku.Proofs
