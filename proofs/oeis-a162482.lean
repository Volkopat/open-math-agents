import OMAStatements.S_oeis_a162482

open PowerSeries

private theorem derivative_numeral (m : ℕ) [m.AtLeastTwo] :
    derivative ℚ (no_index (OfNat.ofNat m : ℚ⟦X⟧)) = 0 := by
  rw [← map_ofNat C m]
  exact derivative_C

private theorem coeff_X_derivative (G : ℚ⟦X⟧) (k : ℕ) :
    coeff k (X * derivative ℚ G) = (k : ℚ) * coeff k G := by
  cases k with
  | zero => simp
  | succ k =>
    rw [coeff_succ_X_mul, coeff_derivative, mul_comm]
    simp only [Nat.cast_add, Nat.cast_one]

private theorem coeff_shift (f : ℚ⟦X⟧) (d k : ℕ) (h : k ≤ d) :
    coeff d (X ^ k * f) = coeff (d - k) f := by
  rw [coeff_X_pow_mul', if_pos h]

private theorem ne_zero_of_const (f : ℚ⟦X⟧) (h : constantCoeff f ≠ 0) : f ≠ 0 := by
  intro hf
  apply h
  rw [hf, map_zero]

private theorem key (T G F : ℚ⟦X⟧)
    (hSq : T ^ 2 * (1 - X) ^ 6 = (1 - X) ^ 6 - 2 * X * (1 - X) ^ 3 - 3 * X ^ 2)
    (hG : 2 * X ^ 2 * G = (1 - X) ^ 3 * (1 - T) - X)
    (hF : F = X * derivative ℚ G) :
    C 2 * (X ^ 0 * F) -
      C 16 * (X ^ 1 * F) +
      C 36 * (X ^ 2 * F) -
      C 52 * (X ^ 3 * F) +
      C 34 * (X ^ 4 * F) -
      C 12 * (X ^ 5 * F) +
      C 2 * (X ^ 6 * F) +
      C 4 * (X ^ 0 * G) -
      C 24 * (X ^ 1 * G) +
      C 36 * (X ^ 2 * G) -
      C 26 * (X ^ 3 * G) +
      C 6 * (X ^ 5 * G) -
      C 2 * (X ^ 6 * G) = 4 - C 12 * X ^ 2 + C 8 * X ^ 3 := by
  have hR : ((1 - X) ^ 3 - X - 2 * X ^ 2 * G) ^ 2 = ((1 - X) ^ 6 - 2 * X * (1 - X) ^ 3 - 3 * X ^ 2) := by
    have h1 : (1 - X) ^ 3 - X - 2 * X ^ 2 * G = (1 - X) ^ 3 * T := by
      linear_combination -hG
    rw [h1]
    linear_combination hSq
  have hd := congrArg (fun f : ℚ⟦X⟧ => derivative ℚ f) hR
  simp [derivative_numeral, Derivation.leibniz, Derivation.leibniz_pow, smul_eq_mul, nsmul_eq_mul] at hd
  have h2X : (2 * X : ℚ⟦X⟧) ≠ 0 :=
    mul_ne_zero (ne_zero_of_const _ (by rw [map_ofNat]; norm_num)) X_ne_zero
  simp only [map_ofNat]
  apply mul_left_cancel₀ h2X
  linear_combination (-((1 - X) ^ 3 - X - 2 * X ^ 2 * G)) * hd +
    (2 * (-(3 * (1 - X) ^ 2) - 1 - 4 * X * G - 2 * X ^ 2 * derivative ℚ G)) * hR +
    (4 * X * ((1 - X) ^ 6 - 2 * X * (1 - X) ^ 3 - 3 * X ^ 2)) * hF

theorem OMA.solution : type_of% @OMA.S_oeis_a162482.main := by
  intro T G hSq _ hG n hn
  obtain ⟨k, rfl⟩ : ∃ k, n = k + 6 := ⟨n - 6, by omega⟩
  have hc := congrArg (coeff (k + 6)) (key T G _ hSq hG rfl)
  have h4 : coeff (k + 6) (4 : ℚ⟦X⟧) = 0 := by
    rw [← map_ofNat C 4, coeff_C, if_neg (by omega)]
  simp (disch := omega) only [map_add, map_sub, map_neg, neg_mul, coeff_C_mul, coeff_shift,
    coeff_X_derivative, coeff_X_pow, if_neg, h4] at hc
  simp only [show k + 6 - 1 = k + 5 by omega, show k + 6 - 2 = k + 4 by omega, show k + 6 - 3 = k + 3 by omega, show k + 6 - 4 = k + 2 by omega, show k + 6 - 5 = k + 1 by omega, show k + 6 - 6 = k by omega, Nat.sub_zero] at hc ⊢
  push_cast at hc ⊢
  linear_combination (1 / 2 : ℚ) * hc
