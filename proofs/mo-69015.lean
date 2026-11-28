import OMAStatements.S_mo_69015
import Mathlib

open OMA.S_mo_69015 in
theorem OMA.disproof : ¬ (type_of% @OMA.S_mo_69015.main) := fun h => by
  have := h.1 2 two_pos (Matrix.diagonal ![1, 2]) (.single 0 1) ⟨by simp [unit], by simp [unit], fun w hw => by
    simp [bilinear, unit, Fin.sum_univ_two, Matrix.vecHead, Matrix.vecTail] at hw ⊢; nlinarith [sq_nonneg (w 0 - 1), sq_nonneg (w 1)]⟩ (.single 1 1) (by simp [unit])
  norm_num [objective, bilinear, Matrix.vecHead, Matrix.vecTail] at this
