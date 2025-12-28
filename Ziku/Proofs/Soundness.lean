import Ziku.IR.Eval
import Ziku.Infer

namespace Ziku.Proofs

/-!
# Type Soundness

This module contains proofs about type soundness.
Note: Since `infer` is marked as `partial`, formal proofs are limited.
-/

-- Utility lemmas
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

end Ziku.Proofs
