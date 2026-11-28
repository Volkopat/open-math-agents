import OMAStatements.S_oeis_a104625

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
  intro h
  have hc := congrArg (constantCoeff (R := ℚ)) h
  norm_num [map_ofNat] at hc

private theorem generating_function_ode (S G : ℚ⟦X⟧)
    (hSq : S ^ 2 = 1 - 4 * X)
    (hG : G * (S - X ^ 2) = 1) :
    let E := X * derivative ℚ G
    (E + X ^ 1 * E - C 56 * (X ^ 2 * E) + C 144 * (X ^ 3 * E) - X ^ 4 * E - C 5 * (X ^ 5 * E) +
        C 36 * (X ^ 6 * E)) +
      (-C 2 * (X ^ 1 * G) - C 10 * (X ^ 2 * G) +
        C 72 * (X ^ 3 * G) - C 4 * (X ^ 4 * G) - C 22 * (X ^ 5 * G) + C 126 * (X ^ 6 * G)) = C 2 * X ^ 2 + C 12 * X ^ 3 - C 54 * X ^ 4 := by
  dsimp only
  have hSqDerivative : 2 * S * derivative ℚ S = -4 := by
    have hd := congrArg (derivative ℚ) hSq
    simp [derivative_numeral, Derivation.leibniz, Derivation.leibniz_pow, smul_eq_mul] at hd
    linear_combination hd
  have hRad : (1 - 4 * X) * derivative ℚ S = (-2) * S := by
    apply mul_left_cancel₀ series_two_ne_zero
    linear_combination S * hSqDerivative - 2 * derivative ℚ S * hSq
  -- Rationalize the generating function before differentiating.
  have hRat : (X ^ 4 + 4 * X - 1) * G = -X ^ 2 - S := by
    linear_combination -(S + X ^ 2) * hG + G * hSq
  have hd := congrArg (derivative ℚ) hRat
  simp [derivative_numeral, Derivation.leibniz, Derivation.leibniz_pow, smul_eq_mul] at hd
  simp only [map_ofNat]
  linear_combination (-X * (1 - 4 * X) * (9 * X + 1)) * hd -
    (2 * X * (9 * X + 1)) * hRat + (X * (9 * X + 1)) * hRad

theorem OMA.solution : type_of% @OMA.S_oeis_a104625.main := by
  intro S G hSq _ hG n hn
  obtain ⟨k, rfl⟩ : ∃ k, n = k + 6 := ⟨n - 6, by omega⟩
  have hc := congrArg (coeff (k + 6)) (generating_function_ode S G hSq hG)
  simp only [map_add, map_sub, coeff_C_mul, coeff_X_pow_mul',
    coeff_X_pow, coeff_X_derivative] at hc
  simp (disch := omega) [show k + 6 - 1 = k + 5 by omega,
    show k + 6 - 2 = k + 4 by omega,
    show k + 6 - 3 = k + 3 by omega,
    show k + 6 - 4 = k + 2 by omega,
    show k + 6 - 5 = k + 1 by omega,
    show k + 6 - 6 = k by omega] at hc
  simp only [show k + 6 - 1 = k + 5 by omega,
    show k + 6 - 2 = k + 4 by omega,
    show k + 6 - 3 = k + 3 by omega,
    show k + 6 - 4 = k + 2 by omega,
    show k + 6 - 5 = k + 1 by omega,
    show k + 6 - 6 = k by omega]
  push_cast at hc ⊢
  linear_combination hc
