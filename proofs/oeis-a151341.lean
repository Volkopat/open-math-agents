import OMAStatements.S_oeis_a151341
import Mathlib

open OMA.S_oeis_a151341 in
theorem OMA.solution : type_of% @OMA.S_oeis_a151341.main := by
  intro n hn
  obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le' hn
  have r (j : ℕ) : ((j:ℚ)+2) * catalan (j+1) = 2*(2*j+1) * catalan j := by
    have h1 := succ_mul_catalan_eq_centralBinom (j+1)
    have h2 := succ_mul_catalan_eq_centralBinom j
    have h3 := j.succ_mul_centralBinom_succ
    qify at h1 h2 h3
    exact mul_left_cancel₀ (by positivity : (j:ℚ)+1 ≠ 0) (by linear_combination (j+1)*h1 + h3 - 2*(2*j+1)*h2)
  have m : ((k:ℚ)+4) * motzkin (k+2) = (2*k+5) * motzkin (k+1) + 3*(k+1) * motzkin k := by
    rw [motzkin]
    field_simp
  have r1 := r (k+1)
  simp [a, add_assoc] at r1 ⊢
  linear_combination (k+2)*(k+4)*motzkin (k+2)*r1 + 2*(k+2)*(2*k+3)*catalan (k+1)*m
    + 6*(k+1)*(2*k+3)*motzkin k*r k
