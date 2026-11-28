import OMAStatements.S_oeis_a105864

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

private theorem series_two_ne_zero : (2 : ℚ⟦X⟧) ≠ 0 := by
  rw [← map_ofNat C 2]
  intro h
  have hc := congrArg (fun f : ℚ⟦X⟧ => constantCoeff f) h
  change constantCoeff (C (2 : ℚ)) = constantCoeff (0 : ℚ⟦X⟧) at hc
  norm_num at hc

private theorem generating_function_ode (c : ℚ) (T G : ℚ⟦X⟧)
    (hSq : T ^ 2 * (1 - C c * X ^ 2) = 1 - 4 * X - C c * X ^ 2)
    (hG : 2 * X * G = 1 - T) :
    (X * derivative ℚ G - C 4 * (X * (X * derivative ℚ G)) -
      C (2 * c) * (X ^ 2 * (X * derivative ℚ G)) +
      C (4 * c) * (X ^ 3 * (X * derivative ℚ G)) +
      C (c ^ 2) * (X ^ 4 * (X * derivative ℚ G))) +
    (G - C 2 * (X * G) - C (2 * c) * (X ^ 2 * G) +
      C (6 * c) * (X ^ 3 * G) + C (c ^ 2) * (X ^ 4 * G)) =
    1 + C c * X ^ 2 := by
  have hd := congrArg (fun f : ℚ⟦X⟧ => derivative ℚ f) hSq
  simp [derivative_numeral, Derivation.leibniz, smul_eq_mul] at hd
  have hT : (1 - C c * X ^ 2) * (1 - 4 * X - C c * X ^ 2) * derivative ℚ T =
      -2 * (1 + C c * X ^ 2) * T := by
    apply mul_left_cancel₀ series_two_ne_zero
    linear_combination (1 - C c * X ^ 2) * T * hd -
      (2 * (1 - C c * X ^ 2) * derivative ℚ T - 2 * C c * X * T) * hSq
  have hg' := congrArg (fun f : ℚ⟦X⟧ => derivative ℚ f) hG
  simp [derivative_numeral, Derivation.leibniz, smul_eq_mul] at hg'
  simp only [map_mul, map_pow, map_ofNat C 4, map_ofNat C 2, map_ofNat C 6]
  apply mul_left_cancel₀ series_two_ne_zero
  linear_combination -hT + (1 - C c * X ^ 2) * (1 - 4 * X - C c * X ^ 2) * hg' +
    2 * (1 + C c * X ^ 2) * hG

theorem OMA.solution : type_of% @OMA.S_oeis_a105864.main := by
  intro T G hSq _ hG n hn
  obtain ⟨k, rfl⟩ : ∃ k, n = k + 4 := ⟨n - 4, by omega⟩
  have hSq' : T ^ 2 * (1 - C (1 : ℚ) * X ^ 2) = 1 - 4 * X - C (1 : ℚ) * X ^ 2 := by
    simpa using hSq
  have hc := congrArg (coeff (k + 4)) (generating_function_ode 1 T G hSq' hG)
  simp only [map_add, map_sub, coeff_C_mul, coeff_X_pow_mul', coeff_succ_X_mul,
    if_pos (show 2 ≤ k + 4 by omega), if_pos (show 3 ≤ k + 4 by omega),
    coeff_one, coeff_X_pow, if_neg (show k + 4 ≠ 0 by omega),
    if_neg (show k + 4 ≠ 2 by omega), if_pos (show 4 ≤ k + 4 by omega),
    mul_zero, add_zero] at hc
  simp only [show k + 4 - 1 = k + 3 by omega, show k + 4 - 2 = k + 2 by omega,
    show k + 4 - 3 = k + 1 by omega, show k + 4 - 4 = k by omega] at hc ⊢
  simp only [coeff_X_derivative, coeff_derivative] at hc
  push_cast at hc ⊢
  linear_combination hc
