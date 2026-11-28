import OMAStatements.S_mo_47888
import Mathlib

open OMA.S_mo_47888 in
theorem OMA.disproof : ¬ (type_of% @OMA.S_mo_47888.main) := fun h => by
  have := h 1 3 one_pos (by decide) (fun x => max 0 ((x 1 : ℝ) - x 2) • ![0, 1, -1]) (fun x y => by simp [Fin.sum_univ_three, max_def]; split_ifs <;> norm_cast at * <;> (try simp [Int.subNatNat_self]) <;> nlinarith [sq_nonneg (x 1 - x 2 - (y 1 - y 2))]) ![1, 0, 0] ![0, 1/4, 3/4] ⟨by simp [Fin.forall_fin_succ], by simp [Fin.sum_univ_three]⟩ ⟨by norm_num [Fin.forall_fin_succ], by norm_num [Fin.sum_univ_succ]⟩
  norm_num [smooth, average, bump, Fin.sum_univ_three, max_def, Fin.ext_iff, Matrix.cons_val_two, Matrix.vecHead, Matrix.vecTail] at this
