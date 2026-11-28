import OMAStatements.S_oeis_a115967

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

private theorem generating_function_ode (S G : ℚ⟦X⟧)
    (hSq : S ^ 2 = 1 - 2 * X - 3 * X ^ 2)
    (hG : G * (2 * S - 1) = 1) :
    C 3 * derivative ℚ G - C 14 * (X * derivative ℚ G) -
      C 5 * (X * (X * derivative ℚ G)) + C 48 * (X * (X * (X * derivative ℚ G))) +
      C 36 * (X * (X * (X * (X * derivative ℚ G)))) - C 5 * G - C 7 * (X * G) +
      C 36 * (X * (X * G)) + C 36 * (X * (X * (X * G))) = 1 + C 3 * X := by
  have hTwo : (2 : ℚ⟦X⟧) ≠ 0 := by
    rw [← map_ofNat C 2]
    intro h
    have hc := congrArg (fun f : ℚ⟦X⟧ => constantCoeff f) h
    change constantCoeff (C (2 : ℚ)) = constantCoeff (0 : ℚ⟦X⟧) at hc
    norm_num at hc
  have hSqDerivative : 2 * S * derivative ℚ S = -2 - 6 * X := by
    have hd := congrArg (fun f : ℚ⟦X⟧ => derivative ℚ f) hSq
    simp [derivative_numeral, Derivation.leibniz, smul_eq_mul] at hd
    linear_combination hd
  have hRadicalODE : (1 - 2 * X - 3 * X ^ 2) * derivative ℚ S = (-1 - 3 * X) * S := by
    apply mul_left_cancel₀ hTwo
    linear_combination S * hSqDerivative - 2 * derivative ℚ S * hSq
  have hS : 2 * S = G * (3 - 8 * X - 12 * X ^ 2) - 1 := by
    linear_combination -(2 * S + 1) * hG + 4 * G * hSq
  have hSDerivative :
      2 * derivative ℚ S =
        derivative ℚ G * (3 - 8 * X - 12 * X ^ 2) + G * (-8 - 24 * X) := by
    have hd := congrArg (fun f : ℚ⟦X⟧ => derivative ℚ f) hS
    simp [derivative_numeral, Derivation.leibniz, smul_eq_mul] at hd
    linear_combination hd
  have hCombined :
      (1 - 2 * X - 3 * X ^ 2) * (2 * derivative ℚ S) = (-1 - 3 * X) * (2 * S) := by
    linear_combination 2 * hRadicalODE
  rw [hSDerivative, hS] at hCombined
  rw [map_ofNat C 3, map_ofNat C 14, map_ofNat C 5, map_ofNat C 48,
    map_ofNat C 36, map_ofNat C 7]
  linear_combination hCombined

theorem OMA.solution : type_of% @OMA.S_oeis_a115967.main := by
  intro S G hSq _ hG n hn
  obtain ⟨k, rfl⟩ : ∃ k, n = k + 4 := ⟨n - 4, by omega⟩
  have hc := congrArg (coeff (k + 3)) (generating_function_ode S G hSq hG)
  simp only [map_add, map_sub, coeff_C_mul, coeff_one, coeff_X_derivative,
    coeff_succ_X_mul, coeff_derivative, coeff_X, if_false,
    show k + 3 ≠ 0 by omega, show k + 3 ≠ 1 by omega, mul_zero, add_zero] at hc
  simp only [show k + 4 - 1 = k + 3 by omega, show k + 4 - 2 = k + 2 by omega,
    show k + 4 - 3 = k + 1 by omega, show k + 4 - 4 = k by omega]
  push_cast at hc ⊢
  linear_combination hc
