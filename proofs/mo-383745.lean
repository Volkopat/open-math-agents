import OMAStatements.S_mo_383745
import Mathlib

open OMA.S_mo_383745 in
theorem OMA.disproof : ¬ (type_of% @OMA.S_mo_383745.main) := fun h => by
  obtain ⟨a, -, -, ha⟩ := h 3 !![1, -1 / 2, -1 / 2; -1 / 2, 1, -1 / 2; -1 / 2, -1 / 2, 1] ⟨.ext fun i j => by fin_cases i <;> fin_cases j <;> rfl, fun v => by
    simp [quadratic, Fin.sum_univ_three]; nlinarith [sq_nonneg (v 0 - v 1), sq_nonneg (v 0 - v 2), sq_nonneg (v 1 - v 2)]⟩ fun i => by fin_cases i <;> rfl
  have e : Real.arcsin (1 / 2) = Real.pi / 6 := by
    rw [← Real.sin_pi_div_six, Real.arcsin_sin] <;> linarith [Real.pi_pos]
  have := ha fun _ => 1
  norm_num [quadratic, entryArcsine, Fin.sum_univ_three, Real.arcsin_neg, e, Matrix.cons_val_two, Matrix.tail_cons, Matrix.head_cons] at this
  linarith [Real.pi_pos]
