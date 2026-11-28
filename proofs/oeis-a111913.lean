import OMAStatements.S_oeis_a111913

-- Problem: A111913, the expansion has period 24.
-- Credit: @ShoQo
-- Proof: Q = (x-1)(x+1)(x^8-x^4+1) divides x^24 - 1, with cofactor
-- R = (x^10+x^8+x^6+x^4+x^2+1)(x^4+1). So f = P/Q satisfies f (x^24 - 1) = P R, a polynomial of
-- degree 23, and the coefficient of x^(n+24) gives a(n) - a(n+24) = 0.

open OMA.S_oeis_a111913 PowerSeries

theorem OMA.solution : type_of% @OMA.S_oeis_a111913.main := by
  intro n
  set P : ℚ⟦X⟧ := X * (-2 - 3 * X - X ^ 2 + X ^ 7 + X ^ 8 + 2 * X ^ 4)
  set Q : ℚ⟦X⟧ := (X - 1) * (X + 1) * (X ^ 8 - X ^ 4 + 1)
  let Pp : Polynomial ℚ := Polynomial.X * (-2 - 3 * Polynomial.X - Polynomial.X ^ 2 +
    Polynomial.X ^ 7 + Polynomial.X ^ 8 + 2 * Polynomial.X ^ 4)
  let Rp : Polynomial ℚ := (Polynomial.X ^ 10 + Polynomial.X ^ 8 + Polynomial.X ^ 6 +
    Polynomial.X ^ 4 + Polynomial.X ^ 2 + 1) * (Polynomial.X ^ 4 + 1)
  have h2 : ((2 : Polynomial ℚ) : ℚ⟦X⟧) = 2 := map_ofNat Polynomial.coeToPowerSeries.ringHom 2
  have h3 : ((3 : Polynomial ℚ) : ℚ⟦X⟧) = 3 := map_ofNat Polynomial.coeToPowerSeries.ringHom 3
  have hP : ((Pp : Polynomial ℚ) : ℚ⟦X⟧) = P := by simp [Pp, P, h2, h3]
  have hR : ((Rp : Polynomial ℚ) : ℚ⟦X⟧) = (X ^ 10 + X ^ 8 + X ^ 6 + X ^ 4 + X ^ 2 + 1) * (X ^ 4 + 1) := by
    simp [Rp]
  have hQ0 : constantCoeff Q ≠ 0 := by simp [Q]
  have hQR : Q * (Rp : ℚ⟦X⟧) = X ^ 24 - 1 := by rw [hR]; simp only [Q]; ring
  have key : P * Q⁻¹ * (X ^ 24 - 1) = ((Pp * Rp : Polynomial ℚ) : ℚ⟦X⟧) := by
    rw [← hQR, Polynomial.coe_mul (φ := Pp) (ψ := Rp), hP,
      show P * Q⁻¹ * (Q * (Rp : ℚ⟦X⟧)) = P * (Q⁻¹ * Q) * Rp by ring,
      PowerSeries.inv_mul_cancel Q hQ0, mul_one]
  have hdeg : (Pp * Rp).natDegree < n + 24 := by
    have : (Pp * Rp).natDegree ≤ 23 := by
      refine Polynomial.natDegree_mul_le.trans ?_
      have h1 : Pp.natDegree ≤ 9 := by simp only [Pp]; compute_degree
      have h2 : Rp.natDegree ≤ 14 := by simp only [Rp]; compute_degree
      omega
    omega
  have h := congrArg (coeff (n + 24)) key
  rw [mul_sub, mul_one, map_sub, coeff_mul_X_pow, Polynomial.coeff_coe,
    Polynomial.coeff_eq_zero_of_natDegree_lt hdeg, sub_eq_zero] at h
  exact h.symm
