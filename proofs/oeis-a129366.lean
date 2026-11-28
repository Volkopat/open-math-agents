import OMAStatements.S_oeis_a129366
import Mathlib

open OMA.S_oeis_a129366

namespace P129366

theorem cat_vals : catalan 0 = 1 ∧ catalan 1 = 1 ∧ catalan 2 = 2 ∧ catalan 3 = 5 ∧
    catalan 4 = 14 ∧ catalan 5 = 42 ∧ catalan 6 = 132 := by
  simp only [catalan_eq_centralBinom_div, Nat.centralBinom_eq_two_mul_choose]
  decide

theorem a_vals : a 0 = 1 ∧ a 1 = 1 ∧ a 2 = 3 ∧ a 3 = 7 ∧ a 4 = 21 ∧ a 5 = 61 ∧ a 6 = 193 := by
  obtain ⟨h0, h1, h2, h3, h4, h5, h6⟩ := cat_vals
  simp only [a, Finset.sum_range_succ, Finset.sum_range_zero]
  norm_num [h0, h1, h2, h3, h4, h5, h6]

end P129366

theorem OMA.disproof : ¬ (type_of% @OMA.S_oeis_a129366.main) := by
  intro h
  have e := h 6 le_rfl
  obtain ⟨h0, h1, h2, h3, h4, h5, h6⟩ := P129366.a_vals
  norm_num [h0, h1, h2, h3, h4, h5, h6] at e
