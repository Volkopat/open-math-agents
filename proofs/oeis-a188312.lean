import OMAStatements.S_oeis_a188312

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
  intro h
  have hc := congrArg (fun f : ℚ⟦X⟧ => constantCoeff f) h
  simp only [map_ofNat, map_zero] at hc
  norm_num at hc

private theorem generating_function_ode (T G : ℚ⟦X⟧)
    (hT : T ^ 2 * ((1 - X) * (1 - X ^ 2)) = (1 - X) * (1 - X ^ 2) - 4 * X)
    (hG : 2 * X * G = (1 - X) * (1 - T)) :
    (X * derivative ℚ G)
      - C 4 * (X ^ 1 * (X * derivative ℚ G))
      - C 6 * (X ^ 2 * (X * derivative ℚ G))
      + (X ^ 4 * (X * derivative ℚ G))
      + G
      - (X ^ 1 * G)
      - C 5 * (X ^ 2 * G)
      - (X ^ 3 * G) =
      1 + X + C 2 * X ^ 2 := by
  have hd : 2 * T * derivative ℚ T * ((1 - X) * (1 - X ^ 2)) + T ^ 2 * (-1 - 2 * X + 3 * X ^ 2) =
      -5 - 2 * X + 3 * X ^ 2 := by
    have h := congrArg (fun f : ℚ⟦X⟧ => derivative ℚ f) hT
    simp [derivative_numeral, Derivation.leibniz, smul_eq_mul, pow_two] at h
    linear_combination h
  have hRadicalODE : ((1 - X) * (1 - X ^ 2) - 4 * X) * ((1 - X) * (1 - X ^ 2)) * derivative ℚ T = -2 * (1 + X ^ 2 - 2 * X ^ 3) * T := by
    apply mul_left_cancel₀ two_ne
    linear_combination (T * ((1 - X) * (1 - X ^ 2))) * hd -
      (2 * ((1 - X) * (1 - X ^ 2)) * derivative ℚ T + T * (-1 - 2 * X + 3 * X ^ 2)) * hT
  have hTd : (1 - X) * derivative ℚ T = T - 1 - 2 * G - 2 * X * derivative ℚ G := by
    have h := congrArg (fun f : ℚ⟦X⟧ => derivative ℚ f) hG
    simp [derivative_numeral, Derivation.leibniz, smul_eq_mul] at h
    linear_combination h
  have hTG : (1 - X) * T = 1 - X - 2 * X * G := by
    linear_combination hG
  have hFactor : (1 - X : ℚ⟦X⟧) ≠ 0 := by
    intro h
    have hc := congrArg (fun f : ℚ⟦X⟧ => constantCoeff f) h
    simp at hc
  rw [map_ofNat C 2, map_ofNat C 4, map_ofNat C 5, map_ofNat C 6]
  apply mul_left_cancel₀ (mul_ne_zero two_ne hFactor)
  linear_combination -hRadicalODE +
    (1 - 5 * X - X ^ 2 + X ^ 3) * (1 + X) * (1 - X) * hTd +
    ((1 - 5 * X - X ^ 2 + X ^ 3) * (1 + X) + 2 * (1 + X + 2 * X ^ 2)) * hTG

theorem OMA.solution : type_of% @OMA.S_oeis_a188312.main := by
  intro T G hT _ hG n hn
  obtain ⟨k, rfl⟩ : ∃ k, n = k + 4 := ⟨n - 4, by omega⟩
  have hc := congrArg (coeff (k + 4)) (generating_function_ode T G hT hG)
  have h1 : ∀ f : ℚ⟦X⟧, coeff (k + 4) (X ^ 1 * f) = coeff (k + 3) f :=
    fun f => coeff_X_pow_mul f 1 (k + 3)
  have h2 : ∀ f : ℚ⟦X⟧, coeff (k + 4) (X ^ 2 * f) = coeff (k + 2) f :=
    fun f => coeff_X_pow_mul f 2 (k + 2)
  have h3 : ∀ f : ℚ⟦X⟧, coeff (k + 4) (X ^ 3 * f) = coeff (k + 1) f :=
    fun f => coeff_X_pow_mul f 3 (k + 1)
  have h4 : ∀ f : ℚ⟦X⟧, coeff (k + 4) (X ^ 4 * f) = coeff (k + 0) f :=
    fun f => coeff_X_pow_mul f 4 (k + 0)
  simp only [map_add, map_sub, coeff_C_mul, h1, h2, h3, h4, coeff_X_derivative] at hc
  simp [coeff_X_pow, coeff_X, coeff_one] at hc
  simp only [show k + 4 - 1 = k + 3 by omega, show k + 4 - 2 = k + 2 by omega,
    show k + 4 - 3 = k + 1 by omega, show k + 4 - 4 = k by omega]
  push_cast at hc ⊢
  linear_combination hc
