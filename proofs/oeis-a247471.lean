import OMAStatements.S_oeis_a247471
import Mathlib

open PowerSeries in
theorem OMA.solution : type_of% @OMA.S_oeis_a247471.main := by
  intro T G hT hg n hn
  obtain ⟨m, rfl⟩ := Nat.exists_eq_add_of_le' hn
  have e (c : ℕ) [c.AtLeastTwo] : (OfNat.ofNat c : ℚ⟦X⟧) = C (OfNat.ofNat c) := (map_ofNat C c).symm
  have t (i : ℕ) : coeff i (X * derivative ℚ G) = i * coeff i G := by
    cases i <;> simp [coeff_derivative, mul_comm]
  obtain ⟨S, hd⟩ : ∃ S, S = 2*X^3*T - (1-X-X^2) := ⟨_, rfl⟩
  have hS : S^2 = 1 - 2*X - X^2 - 2*X^3 + X^4 := by
    rw [hd]
    linear_combination -4*X^3*hT
  have hG : 2*X^3*G = 1 - 3*X + 3*X^3 + 2*X^4 - X^5 - X^6 + (1 - 2*X - X^2 + 2*X^3 + X^4)*S := by
    rw [hd]
    linear_combination 2*X^3*hg - 2*X^3*(1-X-X^2)*hT
  have h1 := congrArg (derivative ℚ) hS
  have h2 := congrArg (derivative ℚ) hG
  simp [e, Derivation.leibniz] at h1 h2
  simp only [map_ofNat] at h1 h2
  have key : 4*(X*derivative ℚ G) - 12*(X*(X*derivative ℚ G)) + 4*(X^3*(X*derivative ℚ G)) + 16*(X^4*(X*derivative ℚ G)) + 4*(X^5*(X*derivative ℚ G)) - 4*(X^6*(X*derivative ℚ G)) + 12*G - 24*(X*G) - 24*(X^3*G) - 8*(X^4*G) - 16*(X^5*G) + 12*(X^6*G) = 24*X^3 - 32*X^4 - 8*X^5 - 8*X^7 := mul_left_cancel₀ (mul_ne_zero (pow_ne_zero 2 X_ne_zero) (fun h => by simpa [e] using congrArg (coeff 0) h : (1 - X - X^2 : ℚ⟦X⟧) ≠ 0)) (by
    linear_combination ((2 - 8*X + 4*X^2 + 8*X^3 + 6*X^4 - 8*X^5 - 12*X^6 + 2*X^8)*h2 - (-6 + 6*X + 24*X^2 + 10*X^3 - 32*X^4 - 54*X^5 - 2*X^6 + 12*X^7)*hG + (1 - 2*X - X^2 + 2*X^3 + X^4)^2*(-((2)*derivative ℚ S + (0)*S)*hS + (1)*S*h1)))
  have h := congrArg (coeff (m+8)) key
  simp [e, coeff_C_mul, t, coeff_X_pow_mul'] at h ⊢
  linear_combination h/(4)
