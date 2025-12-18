import Ziku.Eval

namespace Ziku.Proofs

-- e + 0 = e (when e evaluates)
theorem eval_add_zero_right (env : Env) (e : Expr) (v : Int)
    (h : eval env e = some v) :
    eval env (Expr.add e (Expr.lit 0)) = some v := by
  simp [eval, h]

-- 0 + e = e
theorem eval_add_zero_left (env : Env) (e : Expr) (v : Int)
    (h : eval env e = some v) :
    eval env (Expr.add (Expr.lit 0) e) = some v := by
  simp [eval, h]

-- e - 0 = e
theorem eval_sub_zero (env : Env) (e : Expr) (v : Int)
    (h : eval env e = some v) :
    eval env (Expr.sub e (Expr.lit 0)) = some v := by
  simp [eval, h]

-- e * 1 = e
theorem eval_mul_one_right (env : Env) (e : Expr) (v : Int)
    (h : eval env e = some v) :
    eval env (Expr.mul e (Expr.lit 1)) = some v := by
  simp [eval, h]

-- 1 * e = e
theorem eval_mul_one_left (env : Env) (e : Expr) (v : Int)
    (h : eval env e = some v) :
    eval env (Expr.mul (Expr.lit 1) e) = some v := by
  simp [eval, h]

-- e * 0 = 0 (when e evaluates)
theorem eval_mul_zero_right (env : Env) (e : Expr) (v : Int)
    (h : eval env e = some v) :
    eval env (Expr.mul e (Expr.lit 0)) = some 0 := by
  simp [eval, h]

-- 0 * e = 0
theorem eval_mul_zero_left (env : Env) (e : Expr) (v : Int)
    (h : eval env e = some v) :
    eval env (Expr.mul (Expr.lit 0) e) = some 0 := by
  simp [eval, h]

-- e - e = 0 (when e evaluates deterministically to same value)
theorem eval_sub_self (env : Env) (e : Expr) (v : Int)
    (h : eval env e = some v) :
    eval env (Expr.sub e e) = some 0 := by
  simp [eval, h]

end Ziku.Proofs
