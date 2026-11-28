import OMAStatements.S_oeis_a174013
import Mathlib

open OMA.S_oeis_a174013 PowerSeries in
theorem OMA.solution : type_of% @OMA.S_oeis_a174013.main := by
  intro n hn
  obtain ⟨m, rfl⟩ := Nat.exists_eq_add_of_le' hn
  have e (c : ℕ) [c.AtLeastTwo] : (OfNat.ofNat c : ℚ⟦X⟧) = C (OfNat.ofNat c) := (map_ofNat C c).symm
  have hb : PowerSeries.binomialSeries ℚ (1/2:ℚ)^2 = 1+X := by
    rw [sq, ← PowerSeries.binomialSeries_add, show (1/2+1/2:ℚ) = (1:ℕ) by norm_num, PowerSeries.binomialSeries_nat, pow_one]
  have hS : S^2 = 1 - 2*X - X^2 + 6*X^3 + 5*X^4 := by
    rw [S, ← coe_substAlgHom (HasSubst.of_constantCoeff_zero' (by simp [R])), ← map_pow, hb, map_add, map_one, substAlgHom_X, R]
    ring
  simp only [a]
  generalize hd : ((-1 + 3 * X + X ^ 2 + S) * (2 - 2 * X - 2 * X ^ 2 : ℚ⟦X⟧)⁻¹) = G
  have hG : (2 - 2*X - 2*X^2)*G = -1 + 3*X + X^2 + S := by
    rw [← hd, mul_comm, mul_assoc, PowerSeries.inv_mul_cancel _ (by simp [e]), mul_one]
  have t (i : ℕ) : coeff i (X * derivative ℚ G) = i * coeff i G := by
    cases i <;> simp [coeff_derivative, mul_comm]
  have h1 := congrArg (derivative ℚ) hS
  have h2 := congrArg (derivative ℚ) hG
  simp [e, Derivation.leibniz] at h1 h2
  simp only [map_ofNat] at h1 h2
  have key : 4*(X*derivative ℚ G) + 4*(X*(X*derivative ℚ G)) - 48*(X^2*(X*derivative ℚ G)) + 36*(X^3*(X*derivative ℚ G)) + 144*(X^4*(X*derivative ℚ G)) - 44*(X^5*(X*derivative ℚ G)) - 196*(X^6*(X*derivative ℚ G)) - 80*(X^7*(X*derivative ℚ G)) - 24*(X^3*G) - 120*(X^4*G) - 88*(X^5*G) + 32*(X^6*G) = 4*X + 12*X^2 - 4*X^3 + 48*X^4 - 24*X^5 - 96*X^6 := by
    linear_combination X*(1 + 4*X)*((2 - 4*X - 2*X^2 + 12*X^3 + 10*X^4)*h2 - (-2 - 2*X + 18*X^2 + 20*X^3)*hG + (1)^2*(-((2)*derivative ℚ S + (0)*S)*hS + (1)*S*h1))
  have h := congrArg (coeff (m+8)) key
  simp [e, coeff_C_mul, t, coeff_X_pow_mul'] at h ⊢
  linear_combination h/(4)
