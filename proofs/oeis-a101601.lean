import OMAStatements.S_oeis_a101601

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

theorem OMA.solution : type_of% @OMA.S_oeis_a101601.main := by
  intro S c G hSq _ hc hG n hn
  have hRad : 54 * X ^ 3 * G = 1 - 9 * X - (1 - 3 * X) * S := by
    apply mul_left_cancel₀ (numeral_ne_zero 4)
    linear_combination (216 * X ^ 3) * hG +
      ((6 * X * c) ^ 2 + (6 * X * c) * (1 - S) + (1 - S) ^ 2) * hc + (3 - S) * hSq
  have hSqD : 2 * S * derivative ℚ S = -12 := by
    have hd := congrArg (fun f : ℚ⟦X⟧ => derivative ℚ f) hSq
    simp [derivative_numeral, Derivation.leibniz, Derivation.leibniz_pow, smul_eq_mul,
      nsmul_eq_mul] at hd
    linear_combination hd
  have hSD : (1 - 12 * X) * derivative ℚ S = -6 * S := by
    apply mul_left_cancel₀ (numeral_ne_zero 2)
    linear_combination S * hSqD - 2 * derivative ℚ S * hSq
  have hRadD : 162 * X ^ 2 * G + 54 * X ^ 3 * derivative ℚ G =
      -9 + 3 * S - (1 - 3 * X) * derivative ℚ S := by
    have hd := congrArg (fun f : ℚ⟦X⟧ => derivative ℚ f) hRad
    simp [derivative_numeral, Derivation.leibniz, Derivation.leibniz_pow, smul_eq_mul,
      nsmul_eq_mul] at hd
    linear_combination hd
  have hODE : (1 - 3 * X) * (1 - 12 * X) * (X * derivative ℚ G) +
      (3 - 36 * X + 54 * X ^ 2) * G = 3 := by
    have h54 : (54 : ℚ⟦X⟧) * X ^ 3 ≠ 0 :=
      mul_ne_zero (numeral_ne_zero 54) (pow_ne_zero _ X_ne_zero)
    apply mul_left_cancel₀ h54
    linear_combination ((1 - 3 * X) * (1 - 12 * X) * X) * hRadD +
      (9 * X * (1 - 6 * X)) * hRad - ((1 - 3 * X) ^ 2 * X) * hSD
  let E := X * derivative ℚ G
  have hE : E - C 15 * (X * E) + C 36 * (X ^ 2 * E) + C 3 * G - C 36 * (X * G) +
      C 54 * (X ^ 2 * G) = C 3 := by
    dsimp only [E]
    simp only [map_ofNat]
    linear_combination hODE
  have coeff_E (k : ℕ) : coeff k E = (k : ℚ) * coeff k G := coeff_X_derivative G k
  obtain ⟨k, rfl⟩ : ∃ k : ℕ, n = k + 2 := ⟨n - 2, by omega⟩
  have h := congrArg (fun F : ℚ⟦X⟧ => coeff (k + 2) F) hE
  change coeff (k + 2) _ = coeff (k + 2) _ at h
  simp only [map_add, map_sub, coeff_C_mul, coeff_succ_X_mul, coeff_X_pow_mul, coeff_E,
    coeff_C, if_neg (show k + 2 ≠ 0 by omega)] at h
  rw [show k + 2 - 1 = k + 1 by omega, show k + 2 - 2 = k by omega]
  simp only [Nat.cast_add, Nat.cast_one, Nat.cast_ofNat] at h ⊢
  linear_combination h
