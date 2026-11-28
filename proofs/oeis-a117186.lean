import OMAStatements.S_oeis_a117186

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

private theorem generating_function_ode (S c G : ℚ⟦X⟧)
    (hSq : S ^ 2 = 1 - 4 * X ^ 2)
    (hc : 2 * X ^ 2 * c = 1 - S)
    (hG : G * ((1 - X * c) * S) = (1 + X) * c) :
    -(X * derivative ℚ G) + X * (X * derivative ℚ G) +
      C 6 * (X * (X * (X * derivative ℚ G))) -
      C 4 * (X * (X * (X * (X * derivative ℚ G)))) -
      C 8 * (X * (X * (X * (X * (X * derivative ℚ G))))) - G + C 2 * (X * G) +
      C 8 * (X * (X * G)) - C 12 * (X * (X * (X * G))) -
      C 8 * (X * (X * (X * (X * G)))) = -1 - C 2 * X - X ^ 2 := by
  have hTwo : (2 : ℚ⟦X⟧) ≠ 0 := by
    rw [← map_ofNat C 2]
    intro h
    have hk := congrArg (fun f : ℚ⟦X⟧ => constantCoeff f) h
    change constantCoeff (C (2 : ℚ)) = constantCoeff (0 : ℚ⟦X⟧) at hk
    norm_num at hk
  have hFour : (4 : ℚ⟦X⟧) ≠ 0 := by
    rw [← map_ofNat C 4]
    intro h
    have hk := congrArg (fun f : ℚ⟦X⟧ => constantCoeff f) h
    change constantCoeff (C (4 : ℚ)) = constantCoeff (0 : ℚ⟦X⟧) at hk
    norm_num at hk
  have hX : (X : ℚ⟦X⟧) ≠ 0 := by
    intro h
    have hk := congrArg (coeff 1) h
    simp at hk
  have hcEq : X ^ 2 * c ^ 2 = c - 1 := by
    apply mul_left_cancel₀ (mul_ne_zero hFour (pow_ne_zero 2 hX))
    linear_combination (2 * X ^ 2 * c - 1 - S) * hc + hSq
  have hcNe : c ≠ 0 := by
    intro h
    rw [h] at hcEq
    have hk := congrArg (fun f : ℚ⟦X⟧ => constantCoeff f) hcEq
    simp at hk
  have hGS : 2 * X * (1 - 4 * X ^ 2) * G = (1 + X) * (1 + 2 * X - S) := by
    have hGC : G * (1 - 4 * X ^ 2) = (1 + X) * (1 + X * c) := by
      apply mul_left_cancel₀ hcNe
      linear_combination (1 + X * c) * hG + G * (S - 2) * hcEq + G * (c - 2) * hc
    linear_combination 2 * X * hGC + (1 + X) * hc
  have hS : (1 + X) * S = (1 + 3 * X + 2 * X ^ 2) - (2 * X - 8 * X ^ 3) * G := by
    linear_combination hGS
  have hSDerivative :
      (1 + X) * derivative ℚ S + S =
        (3 + 4 * X) - (2 - 24 * X ^ 2) * G - (2 * X - 8 * X ^ 3) * derivative ℚ G := by
    have hd := congrArg (fun f : ℚ⟦X⟧ => derivative ℚ f) hS
    simp [derivative_numeral, Derivation.leibniz, smul_eq_mul] at hd
    linear_combination hd
  have hSqDerivative : 2 * S * derivative ℚ S = -8 * X := by
    have hd := congrArg (fun f : ℚ⟦X⟧ => derivative ℚ f) hSq
    simp [derivative_numeral, Derivation.leibniz, smul_eq_mul] at hd
    linear_combination hd
  have hRadicalODE : (1 - 4 * X ^ 2) * derivative ℚ S = -4 * X * S := by
    apply mul_left_cancel₀ hTwo
    linear_combination S * hSqDerivative - 2 * derivative ℚ S * hSq
  have hElim :
      (1 - 4 * X - 8 * X ^ 2) * ((1 + X) * S) =
        (1 - 4 * X ^ 2) * (1 + X) * ((1 + X) * derivative ℚ S + S) := by
    linear_combination -(1 + X) ^ 2 * hRadicalODE
  rw [hS, hSDerivative] at hElim
  have hFactor : (1 + 2 * X : ℚ⟦X⟧) ≠ 0 := by
    intro h
    have hk := congrArg (fun f : ℚ⟦X⟧ => constantCoeff f) h
    simp at hk
  rw [map_ofNat C 6, map_ofNat C 4, map_ofNat C 8, map_ofNat C 2, map_ofNat C 12]
  apply mul_left_cancel₀ (mul_ne_zero (neg_ne_zero.mpr hTwo) hFactor)
  linear_combination hElim

theorem OMA.solution : type_of% @OMA.S_oeis_a117186.main := by
  intro S c G hSq _ hc hG n hn
  obtain ⟨k, rfl⟩ : ∃ k, n = k + 4 := ⟨n - 4, by omega⟩
  have hcODE := congrArg (coeff (k + 4)) (generating_function_ode S c G hSq hc hG)
  simp only [map_add, map_sub, map_neg, coeff_C_mul, coeff_one,
    coeff_X_derivative, coeff_succ_X_mul, coeff_derivative, coeff_X, if_false,
    show k + 4 ≠ 0 by omega, show k + 4 ≠ 1 by omega,
    show k + 4 ≠ 2 by omega, coeff_X_pow, mul_zero, sub_zero] at hcODE
  simp only [show k + 4 - 1 = k + 3 by omega, show k + 4 - 2 = k + 2 by omega,
    show k + 4 - 3 = k + 1 by omega, show k + 4 - 4 = k by omega]
  push_cast at hcODE ⊢
  linear_combination hcODE
