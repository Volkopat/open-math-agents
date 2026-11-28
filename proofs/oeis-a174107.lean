import OMAStatements.S_oeis_a174107
import Mathlib

open PowerSeries in
theorem OMA.solution : type_of% @OMA.S_oeis_a174107.main := by
  intro S G hS _ hG n hn
  obtain ⟨m, rfl⟩ := Nat.exists_eq_add_of_le' hn
  have e (c : ℕ) [c.AtLeastTwo] : (OfNat.ofNat c : ℚ⟦X⟧) = C (OfNat.ofNat c) := (map_ofNat C c).symm
  have t (i : ℕ) : coeff i (X * derivative ℚ G) = i * coeff i G := by
    cases i <;> simp [coeff_derivative, mul_comm]
  have h1 := congrArg (derivative ℚ) hS
  have h2 := congrArg (derivative ℚ) hG
  simp [e, Derivation.leibniz] at h1 h2
  simp only [map_ofNat] at h1 h2
  have key : -4*(X*derivative ℚ G) + 24*(X*(X*derivative ℚ G)) - 28*(X^2*(X*derivative ℚ G)) + 24*(X^3*(X*derivative ℚ G)) - 4*(X^4*(X*derivative ℚ G)) - 4*G + 16*(X*G) - 28*(X^2*G) + 32*(X^3*G) - 4*(X^4*G) = -4 + 4*X^2 := by
    linear_combination (exp := 1) ((-2 + 12*X - 14*X^2 + 12*X^3 - 2*X^4)*h2 - (4 - 4*X^2)*hG + (-1)^2*(-((2 - 2*X + 2*X^2)*derivative ℚ S + (-1 + 2*X)*S)*hS + (1 - X + X^2)*S*h1))
  have h := congrArg (coeff (m+4)) key
  simp [e, coeff_C_mul, t, coeff_X_pow_mul'] at h ⊢
  linear_combination h/(-4)
