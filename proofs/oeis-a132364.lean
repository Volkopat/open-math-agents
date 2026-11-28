import OMAStatements.S_oeis_a132364

open PowerSeries

private theorem derivative_numeral (m : ℕ) [m.AtLeastTwo] :
    derivative ℚ (no_index (OfNat.ofNat m : ℚ⟦X⟧)) = 0 := by
  rw [← map_ofNat C m]
  exact derivative_C

private noncomputable def theta1 (G : ℚ⟦X⟧) : ℚ⟦X⟧ := X * derivative ℚ G

private theorem coeff_theta1 (G : ℚ⟦X⟧) (k : ℕ) :
    coeff k (theta1 G) = (k : ℚ) * coeff k G := by
  unfold theta1
  cases k with
  | zero => simp
  | succ k =>
    rw [coeff_succ_X_mul, coeff_derivative, mul_comm]
    simp only [Nat.cast_add, Nat.cast_one]

private theorem coeff_X_pow_mul_le {d n : ℕ} (h : d ≤ n) (f : ℚ⟦X⟧) :
    coeff n (X ^ d * f) = coeff (n - d) f := by
  obtain ⟨m, rfl⟩ := Nat.exists_eq_add_of_le' h
  rw [coeff_X_pow_mul, Nat.add_sub_cancel]

private theorem coeff_X_mul_ge1 {n : ℕ} (h : 1 ≤ n) (f : ℚ⟦X⟧) :
    coeff n (X * f) = coeff (n - 1) f := by
  obtain ⟨m, rfl⟩ := Nat.exists_eq_add_of_le' h
  rw [coeff_succ_X_mul, Nat.add_sub_cancel]

private theorem generating_function_ode (S c G : ℚ⟦X⟧)
    (hSq : S ^ 2 = 1 - 4 * X)
    (hc : 2 * X * c = 1 - S)
    (hG : G * (1 - X ^ 2 * c) = 1) :
    -(theta1 G) + C 5 * (X * theta1 G) -
        C 4 * (X ^ 2 * theta1 G) - (X ^ 3 * theta1 G) +
        C 4 * (X ^ 4 * theta1 G) + G - C 6 * (X * G) + C 2 * (X ^ 2 * G) -
        C 2 * (X ^ 3 * G) + C 6 * (X ^ 4 * G) =
      C 1 - C 6 * X + X ^ 2 * C 1 := by
  have hTwo : (2 : ℚ⟦X⟧) ≠ 0 := by
    rw [← map_ofNat C 2]
    intro h
    have h0 := congrArg (fun f : ℚ⟦X⟧ => constantCoeff f) h
    change constantCoeff (C (2 : ℚ)) = constantCoeff (0 : ℚ⟦X⟧) at h0
    norm_num at h0
  have hRat0 : G * (2 - X + X * S) = 2 := by
    linear_combination 2 * hG + G * X * hc
  have hRat1 : 2 * (1 - X + X ^ 3) * G = 2 - X - X * S := by
    apply mul_left_cancel₀ hTwo
    linear_combination (2 - X - X * S) * hRat0 + G * X ^ 2 * hSq
  have hXS : X * S = 2 - X - 2 * (1 - X + X ^ 3) * G := by
    linear_combination hRat1
  have hSqDeriv : 2 * S * derivative ℚ S = -4 := by
    have hd := congrArg (fun f : ℚ⟦X⟧ => derivative ℚ f) hSq
    simp [derivative_numeral, Derivation.leibniz, smul_eq_mul] at hd
    linear_combination hd
  have hRadicalODE : (1 - 4 * X) * derivative ℚ S = -2 * S := by
    apply mul_left_cancel₀ hTwo
    linear_combination S * hSqDeriv - 2 * derivative ℚ S * hSq
  have hXSDeriv :
      S + X * derivative ℚ S =
        -1 - 2 * (1 - X + X ^ 3) * derivative ℚ G + (2 - 6 * X ^ 2) * G := by
    have hd := congrArg (fun f : ℚ⟦X⟧ => derivative ℚ f) hXS
    simp [derivative_numeral, Derivation.leibniz, smul_eq_mul] at hd
    linear_combination hd
  unfold theta1
  rw [map_ofNat C 5, map_ofNat C 4, map_ofNat C 6, map_ofNat C 2, map_one]
  apply mul_left_cancel₀ hTwo
  linear_combination -((1 - 4 * X) * X * hXSDeriv - X ^ 2 * hRadicalODE - (1 - 6 * X) * hXS)

theorem OMA.solution : type_of% @OMA.S_oeis_a132364.main := by
  intro S c G hSq _ hc hG n hn
  have hcoeff := congrArg (coeff n) (generating_function_ode S c G hSq hc hG)
  have hne0 : n ≠ 0 := by omega
  have hne1 : n ≠ 1 := by omega
  have hne2 : n - 2 ≠ 0 := by omega
  simp only [map_add, map_sub, map_neg, coeff_C_mul,
    coeff_X_pow_mul_le (show 2 ≤ n by omega),
    coeff_X_pow_mul_le (show 3 ≤ n by omega),
    coeff_X_pow_mul_le (show 4 ≤ n by omega),
    coeff_X_mul_ge1 (show 1 ≤ n by omega),
    coeff_C, coeff_X, hne0, hne1, hne2, if_false, mul_zero, add_zero, sub_zero] at hcoeff
  simp only [coeff_theta1] at hcoeff
  simp only [Nat.cast_sub (show 1 ≤ n by omega), Nat.cast_sub (show 2 ≤ n by omega),
    Nat.cast_sub (show 3 ≤ n by omega), Nat.cast_sub (show 4 ≤ n by omega)] at hcoeff
  push_cast at hcoeff ⊢
  linear_combination hcoeff
