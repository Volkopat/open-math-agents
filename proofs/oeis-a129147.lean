import OMAStatements.S_oeis_a129147
import Mathlib

open PowerSeries in
theorem OMA.solution : type_of% @OMA.S_oeis_a129147.main := by
  intro S G hS _ hG n hn
  obtain ⟨m, rfl⟩ := Nat.exists_eq_add_of_le' hn
  have e (c : ℕ) [c.AtLeastTwo] : (OfNat.ofNat c : ℚ⟦X⟧) = C (OfNat.ofNat c) := (map_ofNat C c).symm
  have t (i : ℕ) : coeff i (X * derivative ℚ G) = i * coeff i G := by
    cases i <;> simp [coeff_derivative, mul_comm]
  have h1 := congrArg (derivative ℚ) hS
  have h2 := congrArg (derivative ℚ) hG
  simp [e, Derivation.leibniz] at h1 h2
  simp only [map_ofNat] at h1 h2
  have key : 4*(X*derivative ℚ G) - 8*(X*(X*derivative ℚ G)) - 64*(X^2*(X*derivative ℚ G)) - 64*(X^3*(X*derivative ℚ G)) + 4*G + 8*(X*G) - 48*(X^2*G) - 64*(X^3*G) = 4 + 16*X := by
    linear_combination 2*(1-4*X-8*X^2)*h2 + 2*derivative ℚ S*hS - S*h1 + (4+16*X)*hG
  have h := congrArg (coeff (m+3)) key
  simp [e, coeff_C_mul, t, coeff_X_pow_mul'] at h ⊢
  linear_combination h/4
