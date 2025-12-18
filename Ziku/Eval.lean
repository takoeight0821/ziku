import Ziku.Syntax

namespace Ziku

abbrev Env := List (String × Int)

def eval (env : Env) : Expr → Option Int
  | Expr.lit n => some n
  | Expr.var x => env.lookup x
  | Expr.add e1 e2 =>
    match eval env e1, eval env e2 with
    | some v1, some v2 => some (v1 + v2)
    | _, _ => none
  | Expr.sub e1 e2 =>
    match eval env e1, eval env e2 with
    | some v1, some v2 => some (v1 - v2)
    | _, _ => none
  | Expr.mul e1 e2 =>
    match eval env e1, eval env e2 with
    | some v1, some v2 => some (v1 * v2)
    | _, _ => none
  | Expr.div e1 e2 =>
    match eval env e1, eval env e2 with
    | some v1, some v2 =>
      if v2 == 0 then none
      else some (v1 / v2)
    | _, _ => none

end Ziku
