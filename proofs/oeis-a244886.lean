import OMAStatements.S_oeis_a244886

open PowerSeries

private lemma derivative_numeral (m : ℕ) [m.AtLeastTwo] :
    derivative ℚ (no_index (OfNat.ofNat m : ℚ⟦X⟧)) = 0 := by
  rw [← map_ofNat C m, derivative_C]

private lemma coeff_numeral_mul (m n : ℕ) [m.AtLeastTwo] (F : ℚ⟦X⟧) :
    coeff n (no_index (OfNat.ofNat m : ℚ⟦X⟧) * F) = (OfNat.ofNat m : ℚ) * coeff n F := by
  rw [← map_ofNat C m, coeff_C_mul]

private lemma series_numeral_ne_zero (m : ℕ) [m.AtLeastTwo] :
    (no_index (OfNat.ofNat m : ℚ⟦X⟧)) ≠ 0 := by
  rw [← map_ofNat (C : ℚ →+* ℚ⟦X⟧) m, ← map_zero (C : ℚ →+* ℚ⟦X⟧)]
  exact fun h => Nat.cast_ne_zero.mpr (NeZero.ne m) (C_injective h)

private noncomputable def euler (F : ℚ⟦X⟧) : ℚ⟦X⟧ := X * derivative ℚ F

private lemma coeff_euler (F : ℚ⟦X⟧) (n : ℕ) :
    coeff n (euler F) = coeff n F * (n : ℚ) := by
  cases n with
  | zero => simp [euler]
  | succ n => rw [euler, coeff_succ_X_mul, coeff_derivative, Nat.cast_succ]

private lemma coeff_shift_one (F : ℚ⟦X⟧) (n : ℕ) (hn : 1 ≤ n) :
    coeff n (X * F) = coeff (n - 1) F := by
  rw [← pow_one (X : ℚ⟦X⟧), coeff_X_pow_mul', if_pos hn]

private lemma ne_zero_of_coeff_zero_ne_zero {F : ℚ⟦X⟧} (h : coeff 0 F ≠ 0) : F ≠ 0 :=
  fun h0 => h (by simp [h0])

theorem OMA.solution : type_of% @OMA.S_oeis_a244886.main := by
  intro S G hS hS0 hG n hn
  have hSne : S ≠ 0 := ne_zero_of_coeff_zero_ne_zero (by rw [hS0]; norm_num)
  have hXne : (X : ℚ⟦X⟧) ≠ 0 := fun h => by simpa using congrArg (coeff 1) h
  have hGS : (1 - X) * (-2 + 4 * X + 6 * X ^ 2 + 2 * X ^ 3) * G = (-1 + 3 * X + 2 * X ^ 2) - S := by
    apply mul_left_cancel₀ (mul_ne_zero (series_numeral_ne_zero 2) hXne)
    linear_combination ((1 - 2 * X - X ^ 2) - (1 + X) * S) * hG +
      ((1 - X) * (1 + X) ^ 2 * G - (1 + X)) * hS
  have hdS : (1 - 2 * X - 3 * X ^ 2) * derivative ℚ S = (-1 - 3 * X) * S := by
    have h := congrArg (derivative ℚ) hS
    simp [Derivation.leibniz, smul_eq_mul, derivative_numeral] at h
    apply mul_left_cancel₀ (mul_ne_zero (series_numeral_ne_zero 2) hSne)
    linear_combination (1 - 2 * X - 3 * X ^ 2) * h - 2 * (-1 - 3 * X) * hS
  have hdGS := congrArg (derivative ℚ) hGS
  simp [Derivation.leibniz, smul_eq_mul, derivative_numeral] at hdGS
  have hEuler : euler G - 5 * (X * euler G) + 2 * (X ^ 2 * euler G) +
      13 * (X ^ 3 * euler G) - 8 * (X ^ 5 * euler G) - 3 * (X ^ 6 * euler G) -
      2 * (X * G) + 4 * (X ^ 2 * G) + 9 * (X ^ 3 * G) - 3 * (X ^ 4 * G) -
      19 * (X ^ 5 * G) - 9 * (X ^ 6 * G) -
      (-X + X ^ 2 + 3 * X ^ 3 + 3 * X ^ 4) = 0 := by
    apply mul_left_cancel₀ (series_numeral_ne_zero 2)
    unfold euler
    linear_combination -X * ((1 - 2 * X - 3 * X ^ 2) * hdGS - hdS + (1 + 3 * X) * hGS)
  have h1 : 1 ≤ n := by omega
  have h2 : 2 ≤ n := by omega
  have h3 : 3 ≤ n := by omega
  have h4 : 4 ≤ n := by omega
  have h5 : 5 ≤ n := by omega
  have h6 : 6 ≤ n := by omega
  have hc := congrArg (coeff n) hEuler
  simp only [map_add, map_sub, map_neg, map_zero, coeff_numeral_mul, coeff_shift_one _ _ h1,
    coeff_X_pow_mul', if_pos h2, if_pos h3, if_pos h4, if_pos h5, if_pos h6, coeff_euler,
    coeff_X, coeff_X_pow,
    if_neg (by omega : n ≠ 1), if_neg (by omega : n ≠ 2),
    if_neg (by omega : n ≠ 3), if_neg (by omega : n ≠ 4)] at hc
  rw [Nat.cast_sub h1, Nat.cast_sub h2, Nat.cast_sub h3, Nat.cast_sub h5, Nat.cast_sub h6] at hc
  linear_combination hc
