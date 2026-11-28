import OMAStatements.S_mo_454408
import Mathlib

open Matrix in
theorem OMA.disproof : ¬ (type_of% @OMA.S_mo_454408.main) := fun h => by
  have := h 2 1 two_pos one_pos !![1; 1] !![3 / 5, 4 / 5; 4 / 5, -3 / 5] ![0, 25] (by ext i j; fin_cases i <;> fin_cases j <;> norm_num [mul_apply]) (by simp [Fin.forall_fin_two])
  norm_num [trace, mul_apply, diagonal_apply, Fin.sum_univ_two, vecMul, dotProduct] at this
