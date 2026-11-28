import OMAStatements.S_oeis_a114190

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

private theorem numeral_ne_zero (m : ℕ) [m.AtLeastTwo] (hm : 0 < m) :
    (OfNat.ofNat m : ℚ⟦X⟧) ≠ 0 := by
  rw [← map_ofNat C m]
  intro h
  have hc := congrArg (fun f : ℚ⟦X⟧ => constantCoeff f) h
  simp only [constantCoeff_C, map_zero] at hc
  exact (Nat.cast_ne_zero.mpr (Nat.ne_of_gt hm)) hc

private theorem generating_function_ode (S c G : ℚ⟦X⟧)
    (hSq : S ^ 2 = 1 + 8 * X)
    (hc : -(4 * X * c) = 1 - S)
    (hG : G * (1 + X * (1 - X) * c) = 1) :
    (X * derivative ℚ G)
      + C 7 * (X ^ 1 * (X * derivative ℚ G))
      - C 6 * (X ^ 2 * (X * derivative ℚ G))
      + C 13 * (X ^ 3 * (X * derivative ℚ G))
     
      - C 23 * (X ^ 4 * (X * derivative ℚ G))
      + C 8 * (X ^ 5 * (X * derivative ℚ G))
      - C 3 * (X ^ 1 * G)
      + C 16 * (X ^ 2 * G)
      + C 19 * (X ^ 3 * G)
      - C 26 * (X ^ 4 * G)
      + C 12 * (X ^ 5 * G) = C 20 * X ^ 2
      + C 2 * X ^ 3
      - C 4 * X := by
  have hRadical : (1 + 8 * X) * derivative ℚ S = 4 * S := by
    have hd := congrArg (fun f : ℚ⟦X⟧ => derivative ℚ f) hSq
    simp [derivative_numeral, Derivation.leibniz, smul_eq_mul] at hd
    apply mul_left_cancel₀ (numeral_ne_zero 2 (by decide))
    linear_combination S * hd - 2 * derivative ℚ S * hSq
  have hDenom : G * ((3 + X) + (1 - X) * S) = 4 := by
    linear_combination 4 * hG + G * (1 - X) * hc
  -- Multiply the denominator by its conjugate to eliminate the square.
  have hConjugate : (8 + 16 * X ^ 2 - 8 * X ^ 3) * G = 4 * ((3 + X) - (1 - X) * S) := by
    linear_combination ((3 + X) - (1 - X) * S) * hDenom + (1 - X) ^ 2 * G * hSq
  have hd := congrArg (fun f : ℚ⟦X⟧ => derivative ℚ f) hConjugate
  simp [derivative_numeral, Derivation.leibniz, smul_eq_mul] at hd
  simp only [map_ofNat C 2, map_ofNat C 3, map_ofNat C 4, map_ofNat C 6, map_ofNat C 7,
    map_ofNat C 8, map_ofNat C 12, map_ofNat C 13, map_ofNat C 16, map_ofNat C 19,
    map_ofNat C 20, map_ofNat C 23, map_ofNat C 26]
  apply mul_left_cancel₀ (numeral_ne_zero 8 (by decide))
  linear_combination X * ((1 + 7 * X - 8 * X ^ 2) * hd - (3 - 12 * X) * hConjugate -
    4 * (1 - X) ^ 2 * hRadical)

theorem OMA.solution : type_of% @OMA.S_oeis_a114190.main := by
  intro S c G hSq _ hc hG n hn
  obtain ⟨k, rfl⟩ : ∃ k, n = k + 5 := ⟨n - 5, by omega⟩
  have hCoeff := congrArg (coeff (k + 5)) (generating_function_ode S c G hSq hc hG)
  simp (disch := omega) only [map_add, map_sub, coeff_C_mul,
    coeff_X_pow_mul', coeff_X_pow, coeff_X_derivative,
    coeff_X, if_pos, if_neg, mul_zero, sub_zero] at hCoeff
  simp only [show k + 5 - 1 = k + 4 by omega,
    show k + 5 - 2 = k + 3 by omega,
    show k + 5 - 3 = k + 2 by omega,
    show k + 5 - 4 = k + 1 by omega,
    show k + 5 - 5 = k by omega] at hCoeff ⊢
  push_cast at hCoeff ⊢
  linear_combination hCoeff
