import OMAStatements.S_oeis_a034267
import Mathlib

open OMA.S_oeis_a034267 in
theorem OMA.solution : type_of% @OMA.S_oeis_a034267.main := by
  intro n hn
  obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le' hn
  have c (j : ℕ) : ((2*j).choose (j+1) : ℚ) = j/(j+1) * j.centralBinom := by
    rw [div_mul_eq_mul_div, eq_div_iff (by positivity)]
    have := Nat.choose_succ_right_eq (2*j) j
    rw [two_mul, Nat.add_sub_cancel, ← two_mul] at this
    qify [Nat.centralBinom] at this ⊢
    linarith
  have d (j : ℕ) : ((j+1).centralBinom:ℚ) = 2*(2*j+1)/(j+1) * j.centralBinom := by
    rw [div_mul_eq_mul_div, eq_div_iff (by positivity)]
    have := Nat.succ_mul_centralBinom_succ j
    qify at this
    linarith
  simp only [a, c, d, Nat.add_sub_cancel, show k + 2 - 1 = k + 1 from rfl]
  push_cast
  field_simp
  ring
