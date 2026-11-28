import OMAStatements.S_mo_371077
import Mathlib

open Polynomial in
theorem OMA.disproof : ¬ (type_of% @OMA.S_mo_371077.main) := fun h => by
  have := h (C (2/3) * X - C (1/3)) (fun e => by simpa using congrArg (eval 0) e) ⟨fun z hz => by simpa [hz] using (norm_sub_le (2/3 * z) (1/3)).trans (by simp [hz]; norm_num), -1, by simp, by norm_num⟩ 1 (by simp) (by norm_num)
  norm_num [leadingCoeff, natDegree_sub_C] at this
