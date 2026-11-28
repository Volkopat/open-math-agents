import OMAStatements.S_oeis_a110521
import Mathlib

open PowerSeries in
theorem OMA.solution : type_of% @OMA.S_oeis_a110521.main := by
  intro S c G hS _ hc hg n hn
  obtain ⟨m, rfl⟩ := Nat.exists_eq_add_of_le' hn
  have e (c : ℕ) [c.AtLeastTwo] : (OfNat.ofNat c : ℚ⟦X⟧) = C (OfNat.ofNat c) := (map_ofNat C c).symm
  have t (i : ℕ) : coeff i (X * derivative ℚ G) = i * coeff i G := by
    cases i <;> simp [coeff_derivative, mul_comm]
  have hG : (24+24*X^2+12*X^3)*G = 30 - 6*X - (6+6*X)*S := mul_left_cancel₀ X_ne_zero (by
    linear_combination (5-X-(1+X)*S)*(6*X*hg + G*(X+X^2)*hc) + X*G*(1+X)^2*hS)
  have h1 := congrArg (derivative ℚ) hS
  have h2 := congrArg (derivative ℚ) hG
  simp [e, Derivation.leibniz] at h1 h2
  simp only [map_ofNat] at h1 h2
  have key : -288*(X*derivative ℚ G) + 3168*(X*(X*derivative ℚ G)) + 3168*(X^2*(X*derivative ℚ G)) + 3024*(X^3*(X*derivative ℚ G)) + 5040*(X^4*(X*derivative ℚ G)) + 1728*(X^5*(X*derivative ℚ G)) - 1440*(X*G) - 5760*(X^2*G) + 4464*(X^3*G) + 5760*(X^4*G) + 2592*(X^5*G) = -1728*X - 6912*X^2 + 432*X^3 := by
    linear_combination X*((-12 + 132*X + 144*X^2)*h2 - (60 + 216*X)*hG + (-6 - 6*X)^2*(-((2)*derivative ℚ S + (0)*S)*hS + (1)*S*h1))
  have h := congrArg (coeff (m+5)) key
  simp [e, coeff_C_mul, t, coeff_X_pow_mul'] at h ⊢
  linear_combination h/(-144)
