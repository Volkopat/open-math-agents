import OMAStatements.S_mo_58241
import Mathlib

open Matrix in
theorem OMA.disproof : ¬ (type_of% @OMA.S_mo_58241.main) := fun h => by
  have := h 2 !![2 / 5, 3 / 5; 1 / 10, 9 / 10] (by simp [Fin.forall_fin_two]; norm_num) (by simp; norm_num) ⟨1, by simp [Fin.forall_fin_two]⟩ (3 / 10) ![6, -1] (by simp) (by ext i; fin_cases i <;> simp [mulVec, dotProduct] <;> norm_num) 0 1
  norm_num [mulVec, dotProduct, Fin.sum_univ_two, pow_two, mul_apply] at this
