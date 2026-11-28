import OMAStatements.S_oeis_a106181

open PowerSeries

private theorem derivative_numeral (m : ℕ) [m.AtLeastTwo] :
    derivative ℚ (no_index (OfNat.ofNat m : ℚ⟦X⟧)) = 0 := by
  rw [← map_ofNat C m]
  exact derivative_C

private theorem numeral_ne_zero (m : ℕ) [m.AtLeastTwo] :
    (no_index (OfNat.ofNat m : ℚ⟦X⟧)) ≠ 0 := by
  rw [← map_ofNat C m]
  intro h
  have hc := congrArg (fun f : ℚ⟦X⟧ => constantCoeff f) h
  change constantCoeff (C (OfNat.ofNat m : ℚ)) = constantCoeff (0 : ℚ⟦X⟧) at hc
  rw [constantCoeff_C, map_zero] at hc
  exact (OfNat.ofNat_ne_zero m) hc

private theorem coeff_X_derivative (G : ℚ⟦X⟧) (k : ℕ) :
    coeff k (X * derivative ℚ G) = (k : ℚ) * coeff k G := by
  cases k with
  | zero => simp
  | succ k =>
    rw [coeff_succ_X_mul, coeff_derivative, mul_comm]
    simp only [Nat.cast_add, Nat.cast_one]

theorem OMA.solution : type_of% @OMA.S_oeis_a106181.main := by
  intro S c G hSq _ hc hG n hn
  have hRad : 2 * X ^ 2 * G = (1 + X) * S - 1 - X - 2 * X ^ 2 := by
    apply mul_left_cancel₀ (numeral_ne_zero 2)
    linear_combination (2 * X ^ 2) * hG - (1 + 2 * X - S) * hc - hSq
  have hSqD : 2 * S * derivative ℚ S = 8 * X := by
    have hd := congrArg (fun f : ℚ⟦X⟧ => derivative ℚ f) hSq
    simp [derivative_numeral, Derivation.leibniz, Derivation.leibniz_pow, smul_eq_mul,
      nsmul_eq_mul] at hd
    linear_combination hd
  have hSD : (1 + 4 * X ^ 2) * derivative ℚ S = 4 * X * S := by
    apply mul_left_cancel₀ (numeral_ne_zero 2)
    linear_combination S * hSqD - 2 * derivative ℚ S * hSq
  have hRadD : 4 * X * G + 2 * X ^ 2 * derivative ℚ G =
      S + (1 + X) * derivative ℚ S - 1 - 4 * X := by
    have hd := congrArg (fun f : ℚ⟦X⟧ => derivative ℚ f) hRad
    simp [derivative_numeral, Derivation.leibniz, Derivation.leibniz_pow, smul_eq_mul,
      nsmul_eq_mul] at hd
    linear_combination hd
  have hODE : (1 + X) * (1 + 4 * X ^ 2) * (X * derivative ℚ G) +
      (2 + X + 4 * X ^ 2) * G = 3 * X - 2 * X ^ 2 := by
    have h2 : (2 : ℚ⟦X⟧) * X ^ 2 ≠ 0 :=
      mul_ne_zero (numeral_ne_zero 2) (pow_ne_zero _ X_ne_zero)
    apply mul_left_cancel₀ h2
    linear_combination ((1 + X) * (1 + 4 * X ^ 2) * X) * hRadD -
      (X + 4 * X ^ 2 + 8 * X ^ 3) * hRad + ((1 + X) ^ 2 * X) * hSD
  let E := X * derivative ℚ G
  have hE : E + X * E + C 4 * (X ^ 2 * E) + C 4 * (X ^ 3 * E) + C 2 * G + X * G +
      C 4 * (X ^ 2 * G) = C 3 * X ^ 1 - C 2 * X ^ 2 := by
    dsimp only [E]
    simp only [map_ofNat]
    linear_combination hODE
  have coeff_E (k : ℕ) : coeff k E = (k : ℚ) * coeff k G := coeff_X_derivative G k
  obtain ⟨k, rfl⟩ : ∃ k : ℕ, n = k + 3 := ⟨n - 3, by omega⟩
  have h := congrArg (fun F : ℚ⟦X⟧ => coeff (k + 3) F) hE
  change coeff (k + 3) _ = coeff (k + 3) _ at h
  have e2 : coeff (k + 3) (X ^ 2 * E) = coeff (k + 1) E := coeff_X_pow_mul E 2 (k + 1)
  have g2 : coeff (k + 3) (X ^ 2 * G) = coeff (k + 1) G := coeff_X_pow_mul G 2 (k + 1)
  simp only [map_add, map_sub, coeff_C_mul, coeff_succ_X_mul, e2, g2] at h
  simp only [coeff_X_pow_mul, coeff_E, coeff_X_pow,
    if_neg (show k + 3 ≠ 1 by omega), if_neg (show k + 3 ≠ 2 by omega), mul_zero,
    sub_zero] at h
  rw [show k + 3 - 1 = k + 2 by omega, show k + 3 - 2 = k + 1 by omega,
    show k + 3 - 3 = k by omega]
  simp only [Nat.cast_add, Nat.cast_one, Nat.cast_ofNat] at h ⊢
  linear_combination h
