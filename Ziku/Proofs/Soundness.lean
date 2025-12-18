import Ziku.Eval
import Ziku.Infer

namespace Ziku.Proofs

-- Basic type inference properties

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

-- Utility lemmas

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

end Ziku.Proofs
