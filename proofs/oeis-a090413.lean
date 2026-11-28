import OMAStatements.S_oeis_a090413

open PowerSeries OMA.S_oeis_a090413 in
theorem OMA.solution : type_of% @OMA.S_oeis_a090413.main := by
  have hsub : HasSubst (-(X : PowerSeries ℚ) ^ 2) := .of_constantCoeff_zero' (by simp)
  have hcatQ : (catalanSeries.map (Nat.castRingHom ℚ)) ^ 2 * X + 1 =
      catalanSeries.map (Nat.castRingHom ℚ) := by
    simpa [PowerSeries.map_X] using
      congrArg (PowerSeries.map (Nat.castRingHom ℚ)) catalanSeries_sq_mul_X_add_one
  have hcat : catNeg ^ 2 * (-X ^ 2) + 1 = catNeg := by
    have h := congrArg (substAlgHom hsub) hcatQ
    rw [map_add, map_mul, map_pow, map_one, substAlgHom_X] at h
    simpa [coe_substAlgHom, catNeg] using h
  have hrel : series * (1 - 3 * X * catNeg) = catNeg :=
    (PowerSeries.eq_mul_inv_iff_mul_eq (by simp)).mp rfl
  set c := catNeg
  set S := series
  have hq : (3 * X - 8 * X ^ 2) * S ^ 2 + (1 - 6 * X) * S - 1 = 0 := by
    linear_combination (1 + 3 * X * S + 2 * X ^ 2 * S - X ^ 2 * (S * (1 - 3 * X * c) - c)) *
      hrel - (1 + 3 * X * S) ^ 2 * hcat
  have hd : (3 - 16 * X) * S ^ 2 + (3 * X - 8 * X ^ 2) * (2 * S * d⁄dX ℚ S) - 6 * S +
      (1 - 6 * X) * d⁄dX ℚ S = 0 := by
    have := congrArg (d⁄dX ℚ) hq
    simp [Derivation.leibniz, Derivation.leibniz_pow, ← map_ofNat C] at this
    linear_combination (norm := (simp only [map_ofNat]; ring)) this
  have hode : 3 * X * d⁄dX ℚ S - 8 * X ^ 2 * d⁄dX ℚ S + 12 * X ^ 3 * d⁄dX ℚ S -
      32 * X ^ 4 * d⁄dX ℚ S + 3 * S - 16 * X * S - 32 * X ^ 3 * S = 3 + 2 * X := by
    linear_combination (3 * X - 8 * X ^ 2) * (2 * (3 * X - 8 * X ^ 2) * S + 1 - 6 * X) * hd -
      (4 * (3 * X - 8 * X ^ 2) ^ 2 * d⁄dX ℚ S + 2 * (3 * X - 8 * X ^ 2) * (3 - 16 * X) * S -
        12 * (3 * X - 8 * X ^ 2) - (3 - 16 * X) * (1 - 6 * X)) * hq
  intro n hn
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 3 := ⟨n - 3, by omega⟩
  have := congrArg (coeff (m + 3)) hode
  simp [← map_ofNat C, coeff_C_mul, coeff_X_pow_mul', coeff_derivative, mul_assoc] at this
  rcases m with _ | m <;> simp [term, S] at this ⊢ <;> linear_combination this
