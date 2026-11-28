import OMAStatements.S_oeis_a188314

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

private theorem two_ne : (2 : ℚ⟦X⟧) ≠ 0 := by
  rw [← map_ofNat C 2]
  intro h
  have hc := congrArg (fun f : ℚ⟦X⟧ => constantCoeff f) h
  change constantCoeff (C (2 : ℚ)) = constantCoeff (0 : ℚ⟦X⟧) at hc
  norm_num at hc

private theorem generating_function_ode (T G : ℚ⟦X⟧)
    (hT : T ^ 2 * ((1 - X) * (1 - X ^ 2)) = (1 - X) * (1 - X ^ 2) - 4 * X)
    (hG : 2 * X * G = (1 - X ^ 2) * (1 - T)) :
    C 1 * (X * derivative ℚ G) + C (-4) * (X ^ 1 * (X * derivative ℚ G)) +
      C (-6) * (X ^ 2 * (X * derivative ℚ G)) + C 1 * (X ^ 4 * (X * derivative ℚ G)) +
      C 1 * G + C (-2) * (X ^ 1 * G) + C (-1) * (X ^ 4 * G) =
      C 1 + C 2 * X ^ 1 + C 3 * X ^ 2 + C 2 * X ^ 3 := by
  have hSq : (1 - X ^ 2 - 2 * X * G) ^ 2 = 1 - 4 * X - 6 * X ^ 2 + X ^ 4 := by
    linear_combination (-((1 - X ^ 2 - 2 * X * G) + (1 - X ^ 2) * T)) * hG + (1 + X) * hT
  have hd : (1 - X ^ 2 - 2 * X * G) * (-2 * X - 2 * G - 2 * X * derivative ℚ G) =
      -2 - 6 * X + 2 * X ^ 3 := by
    apply mul_left_cancel₀ two_ne
    have h := congrArg (fun f : ℚ⟦X⟧ => derivative ℚ f) hSq
    simp [derivative_numeral, Derivation.leibniz, Derivation.leibniz_pow, smul_eq_mul] at h
    linear_combination h
  have key : (1 - 4 * X - 6 * X ^ 2 + X ^ 4) * (X + G + X * derivative ℚ G) +
      (-1 - 3 * X + X ^ 3) * (1 - X ^ 2 - 2 * X * G) = 0 := by
    have hm : (-2 : ℚ⟦X⟧) ≠ 0 := neg_ne_zero.mpr two_ne
    apply mul_left_cancel₀ hm
    linear_combination (1 - X ^ 2 - 2 * X * G) * hd -
      (-2 * X - 2 * G - 2 * X * derivative ℚ G) * hSq
  simp only [map_neg, map_ofNat, map_one]
  linear_combination key

theorem OMA.solution : type_of% @OMA.S_oeis_a188314.main := by
  intro T G hT _ hG n hn
  obtain ⟨k, rfl⟩ : ∃ k, n = k + 5 := ⟨n - 5, by omega⟩
  have hode := generating_function_ode T G hT hG
  have h1 := congrArg (coeff (k + 5)) hode
  have h2 := congrArg (coeff (k + 4)) hode
  simp (disch := omega) only [map_add, coeff_C_mul, coeff_C, coeff_X_pow_mul', coeff_X_pow,
    if_pos, if_neg] at h1 h2
  simp only [show k + 5 - 1 = k + 4 by omega, show k + 5 - 2 = k + 3 by omega,
    show k + 5 - 4 = k + 1 by omega, show k + 4 - 1 = k + 3 by omega,
    show k + 4 - 2 = k + 2 by omega, show k + 4 - 4 = k by omega,
    coeff_X_derivative] at h1 h2
  simp only [show k + 5 - 1 = k + 4 by omega, show k + 5 - 2 = k + 3 by omega,
    show k + 5 - 3 = k + 2 by omega, show k + 5 - 4 = k + 1 by omega,
    show k + 5 - 5 = k by omega]
  push_cast at h1 h2 ⊢
  linear_combination h1 + 5 * h2
