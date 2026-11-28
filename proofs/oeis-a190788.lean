import OMAStatements.S_oeis_a190788

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

private theorem key (S G F : ℚ⟦X⟧) (hSq : S ^ 2 = 1 - 4 * X ^ 2)
    (hG : G * ((X - 1) * S + X) = (X - 1) * S) (hF : F = X * derivative ℚ G) :
    -C 1 * (X ^ 0 * F) +
      C 3 * (X ^ 1 * F) +
      C 6 * (X ^ 2 * F) -
      C 24 * (X ^ 3 * F) +
      C 4 * (X ^ 4 * F) +
      C 44 * (X ^ 5 * F) -
      C 48 * (X ^ 6 * F) +
      C 16 * (X ^ 7 * F) +
      C 1 * (X ^ 0 * G) -
      C 2 * (X ^ 1 * G) -
      C 2 * (X ^ 2 * G) +
      C 4 * (X ^ 3 * G) +
      C 4 * (X ^ 4 * G) +
      C 8 * (X ^ 5 * G) -
      C 32 * (X ^ 6 * G) +
      C 16 * (X ^ 7 * G) =
      C 1 * (X ^ 0 * 1) -
      C 2 * (X ^ 1 * 1) -
      C 3 * (X ^ 2 * 1) +
      C 4 * (X ^ 3 * 1) +
      C 4 * (X ^ 4 * 1) +
      C 12 * (X ^ 5 * 1) -
      C 32 * (X ^ 6 * 1) +
      C 16 * (X ^ 7 * 1) := by
  have hTwo : (2 : ℚ⟦X⟧) ≠ 0 := ne_zero_of_const _ (by rw [map_ofNat]; norm_num)
  have hSd : 2 * S * derivative ℚ S = -(8 * X) := by
    have hd := congrArg (fun f : ℚ⟦X⟧ => derivative ℚ f) hSq
    simp [derivative_numeral, Derivation.leibniz, Derivation.leibniz_pow, smul_eq_mul, nsmul_eq_mul] at hd
    linear_combination hd
  have hODE : (1 - 4 * X ^ 2) * derivative ℚ S = -(4 * X * S) := by
    apply mul_left_cancel₀ hTwo
    linear_combination S * hSd - 2 * derivative ℚ S * hSq
  have hY : (1 - 2 * X - 3 * X ^ 2 + 8 * X ^ 3 - 4 * X ^ 4) - (1 - 2 * X - 4 * X ^ 2 + 8 * X ^ 3 - 4 * X ^ 4) * G = X * (X - 1) * S := by
    linear_combination (-((X - 1) * S - X)) * hG + (X - 1) ^ 2 * (G - 1) * hSq
  have hYd := congrArg (fun f : ℚ⟦X⟧ => derivative ℚ f) hY
  simp [derivative_numeral, Derivation.leibniz, Derivation.leibniz_pow, smul_eq_mul, nsmul_eq_mul] at hYd
  simp only [map_ofNat, map_one]
  linear_combination (-(X * (-1 + X + 4 * X ^ 2 - 4 * X ^ 3))) * hYd + (-1 + 2 * X + 8 * X ^ 2 - 12 * X ^ 3) * hY -
    (X * (X - 1)) ^ 2 * hODE + ((-1 + X + 4 * X ^ 2 - 4 * X ^ 3) * (1 - 2 * X - 4 * X ^ 2 + 8 * X ^ 3 - 4 * X ^ 4)) * hF

theorem OMA.solution : type_of% @OMA.S_oeis_a190788.main := by
  intro S G hSq _ hG n hn
  obtain ⟨k, rfl⟩ : ∃ k, n = k + 8 := ⟨n - 8, by omega⟩
  have hc := congrArg (coeff (k + 8)) (key S G _ hSq hG rfl)
  simp (disch := omega) only [map_add, map_sub, map_neg, neg_mul, coeff_C_mul, coeff_shift,
    coeff_X_derivative, coeff_one, if_neg, mul_zero, add_zero, sub_zero, neg_zero] at hc
  simp only [show k + 8 - 1 = k + 7 by omega, show k + 8 - 2 = k + 6 by omega, show k + 8 - 3 = k + 5 by omega, show k + 8 - 4 = k + 4 by omega, show k + 8 - 5 = k + 3 by omega, show k + 8 - 6 = k + 2 by omega, show k + 8 - 7 = k + 1 by omega, show k + 8 - 8 = k by omega, Nat.sub_zero] at hc ⊢
  push_cast at hc ⊢
  linear_combination hc
