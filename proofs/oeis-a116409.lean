import OMAStatements.S_oeis_a116409
import Mathlib

open PowerSeries in
theorem OMA.solution : type_of% @OMA.S_oeis_a116409.main := by
  intro S G hS _ hG n hn
  obtain ⟨m, rfl⟩ := Nat.exists_eq_add_of_le' hn
  have e (c : ℕ) [c.AtLeastTwo] : (OfNat.ofNat c : ℚ⟦X⟧) = C (OfNat.ofNat c) := (map_ofNat C c).symm
  have t (i : ℕ) : coeff i (X * derivative ℚ G) = i * coeff i G := by
    cases i <;> simp [coeff_derivative, mul_comm]
  have h1 := congrArg (derivative ℚ) hS
  have h2 := congrArg (derivative ℚ) hG
  simp [e, Derivation.leibniz] at h1 h2
  simp only [map_ofNat] at h1 h2
  have key : 4*(X*derivative ℚ G) - 24*(X*(X*derivative ℚ G)) + 32*(X^2*(X*derivative ℚ G)) + 24*(X^3*(X*derivative ℚ G)) - 36*(X^4*(X*derivative ℚ G)) - 8*(X*G) + 24*(X^2*G) + 24*(X^3*G) - 72*(X^4*G) = 12*X^3 := mul_left_cancel₀ (fun h => by simpa [e] using congrArg (coeff 0) h : (1 + X : ℚ⟦X⟧) ≠ 0) (by
    linear_combination X*((2 - 4*X - 6*X^2)*h2 - (-2 - 6*X)*hG + (1)^2*(-((2)*derivative ℚ S + (0)*S)*hS + (1)*S*h1)))
  have h := congrArg (coeff (m+4)) key
  simp [e, coeff_C_mul, t, coeff_X_pow_mul'] at h ⊢
  linear_combination h/(4)
