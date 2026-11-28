import OMAStatements.S_mo_202568
import Mathlib

open OMA.S_mo_202568

theorem OMA.disproof : ¬ (type_of% @OMA.S_mo_202568.main) := by
  intro h
  have := h (Fin 2) ![1, 0] ![3 / 4, 1 / 4] (by intro a; fin_cases a <;> norm_num)
    (by intro a; fin_cases a <;> norm_num) (by simp [Fin.sum_univ_two])
    (by simp [Fin.sum_univ_two]; norm_num)
  simp only [entropy, relativeEntropy, Fin.sum_univ_two, Matrix.cons_val_zero,
    Matrix.cons_val_one, Matrix.head_cons, Real.log_one, Real.log_zero] at this
  have h1 : Real.log (1 / 4) < Real.log (3 / 4) := Real.log_lt_log (by norm_num) (by norm_num)
  nlinarith [h1]
