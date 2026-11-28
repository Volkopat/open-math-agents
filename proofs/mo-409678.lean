import OMAStatements.S_mo_409678
import Mathlib

theorem OMA.disproof : ¬ (type_of% @OMA.S_mo_409678.main) := fun h => by
  have := h 3 (by norm_num) (Metric.closedBall 0 1 ∩ {x | 1 ≤ x 0 + x 1 + x 2})
    ((isCompact_closedBall 0 1).inter_right (isClosed_le continuous_const (by fun_prop)))
    ((convex_closedBall 0 1).inter (convex_halfSpace_ge ⟨fun x y => by simp; ring, fun c x => by simp; ring⟩ 1))
    (fun i s hs => ⟨fun j => if j = i then s else 1, by
      rcases hs with rfl | rfl <;> fin_cases i <;> simp [pi_norm_le_iff_of_nonneg, Fin.forall_fin_succ, abs_le]⟩)
  norm_num at this
