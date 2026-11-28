import OMAStatements.S_oeis_a097331

open PowerSeries

private lemma derivative_numeral (m : ℕ) [m.AtLeastTwo] :
    derivative ℚ (no_index (OfNat.ofNat m : ℚ⟦X⟧)) = 0 := by
  rw [← map_ofNat C m, derivative_C]

private lemma coeff_numeral_mul (m n : ℕ) [m.AtLeastTwo] (F : ℚ⟦X⟧) :
    coeff n (no_index (OfNat.ofNat m : ℚ⟦X⟧) * F) = (OfNat.ofNat m : ℚ) * coeff n F := by
  rw [← map_ofNat C m, coeff_C_mul]

private lemma series_two_ne_zero : (2 : ℚ⟦X⟧) ≠ 0 := by
  rw [← map_ofNat (C : ℚ →+* ℚ⟦X⟧) 2, ← map_zero (C : ℚ →+* ℚ⟦X⟧)]
  exact fun h => two_ne_zero (C_injective h)

private noncomputable def euler (F : ℚ⟦X⟧) : ℚ⟦X⟧ := X * derivative ℚ F

private lemma coeff_euler (F : ℚ⟦X⟧) (n : ℕ) :
    coeff n (euler F) = coeff n F * (n : ℚ) := by
  cases n with
  | zero => simp [euler]
  | succ n => rw [euler, coeff_succ_X_mul, coeff_derivative, Nat.cast_succ]

private lemma coeff_shift_one (F : ℚ⟦X⟧) (n : ℕ) (hn : 1 ≤ n) :
    coeff n (X * F) = coeff (n - 1) F := by
  rw [← pow_one (X : ℚ⟦X⟧), coeff_X_pow_mul', if_pos hn]

theorem OMA.solution : type_of% @OMA.S_oeis_a097331.main := by
  intro S G hS hS0 hG n hn
  have hFactor : (1 + S : ℚ⟦X⟧) ≠ 0 := by
    intro h
    have hc := congrArg (coeff 0) h
    have hcS : constantCoeff S = 1 := by
      simpa only [coeff_zero_eq_constantCoeff] using hS0
    norm_num [hcS] at hc
  have hRel : 2 * X * (G - 1) = 1 - S := by
    apply mul_left_cancel₀ (mul_ne_zero hFactor (show (X : ℚ⟦X⟧) ≠ 0 from X_ne_zero))
    linear_combination 2 * X ^ 2 * hG + X * hS
  have hdS := congrArg (derivative ℚ) hS
  simp [Derivation.leibniz, smul_eq_mul, derivative_numeral] at hdS
  have hRadical : (1 - 4 * X ^ 2) * derivative ℚ S = -4 * X * S := by
    apply mul_left_cancel₀ series_two_ne_zero
    linear_combination S * hdS - 2 * derivative ℚ S * hS
  have hdG := congrArg (derivative ℚ) hRel
  simp [Derivation.leibniz, smul_eq_mul, derivative_numeral] at hdG
  have hEuler : euler G + X * euler G - 4 * (X ^ 2 * euler G) -
      4 * (X ^ 3 * euler G) + G + X * G = 1 + 3 * X + 2 * X ^ 2 := by
    unfold euler
    apply mul_left_cancel₀ series_two_ne_zero
    linear_combination (1 + X) * ((1 - 4 * X ^ 2) * hdG - hRadical + 4 * X * hRel)
  have h1 : 1 ≤ n := by omega
  have h2 : 2 ≤ n := by omega
  have hc := congrArg (coeff n) hEuler
  simp only [map_add, map_sub, coeff_numeral_mul, coeff_shift_one _ _ h1,
    coeff_X_pow_mul', if_pos h2, if_pos hn, coeff_euler, coeff_one, coeff_X, coeff_X_pow,
    if_neg (show n ≠ 0 by omega), if_neg (show n ≠ 1 by omega),
    if_neg (show n ≠ 2 by omega), mul_zero, add_zero] at hc
  rw [Nat.cast_sub h1, Nat.cast_sub h2, Nat.cast_sub hn] at hc
  linear_combination hc
