import OMAStatements.S_oeis_a212205
import Mathlib

open PowerSeries in
theorem OMA.solution : type_of% @OMA.S_oeis_a212205.main := by
  intro S G hS _ hG n hn
  obtain ⟨m, rfl⟩ := Nat.exists_eq_add_of_le' hn
  have e (c : ℕ) [c.AtLeastTwo] : (OfNat.ofNat c : ℚ⟦X⟧) = C (OfNat.ofNat c) := (map_ofNat C c).symm
  have t (i : ℕ) : coeff i (X * derivative ℚ G) = i * coeff i G := by
    cases i <;> simp [coeff_derivative, mul_comm]
  have h1 := congrArg (derivative ℚ) hS
  have h2 := congrArg (derivative ℚ) hG
  simp [e, Derivation.leibniz] at h1 h2
  simp only [map_ofNat] at h1 h2
  have key : 4*(X*derivative ℚ G) + 8*(X*(X*derivative ℚ G)) - 48*(X^2*(X*derivative ℚ G)) - 96*(X^3*(X*derivative ℚ G)) + 148*(X^4*(X*derivative ℚ G)) + 296*(X^5*(X*derivative ℚ G)) - 24*(X^6*(X*derivative ℚ G)) - 48*(X^7*(X*derivative ℚ G)) + 4*G - 72*(X^2*G) - 48*(X^3*G) + 284*(X^4*G) + 272*(X^5*G) - 24*(X^6*G) = 4 + 8*X - 40*X^2 - 72*X^3 + 60*X^4 + 48*X^5 - 24*X^6 := by
    linear_combination (exp := 1) ((2 + 4*X - 12*X^2 - 24*X^3 + 2*X^4 + 4*X^5)*h2 - (4 - 12*X - 48*X^2 + 4*X^3 + 12*X^4)*hG + (1 + 2*X)^2*(-((2)*derivative ℚ S + (0)*S)*hS + (1)*S*h1))
  have h := congrArg (coeff (m+7)) key
  simp [e, coeff_C_mul, t, coeff_X_pow_mul'] at h ⊢
  linear_combination h/(4)
