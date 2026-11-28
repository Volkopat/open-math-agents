import OMAStatements.S_oeis_a244884

open PowerSeries

private noncomputable def euler (f : ℚ⟦X⟧) : ℚ⟦X⟧ := X * d⁄dX ℚ f

private theorem coeff_euler (n : ℕ) (f : ℚ⟦X⟧) :
    coeff n (euler f) = coeff n f * (n : ℚ) := by
  cases n with
  | zero => simp [euler, coeff_zero_X_mul]
  | succ n => simp [euler, coeff_derivative, Nat.cast_succ]

private theorem coeff_shift (n k : ℕ) (h : k ≤ n) (f : ℚ⟦X⟧) :
    coeff n (X ^ k * f) = coeff (n - k) f := by
  conv_lhs => rw [← Nat.sub_add_cancel h]
  exact coeff_X_pow_mul f k (n - k)

theorem OMA.solution : type_of% @OMA.S_oeis_a244884.main := by
  intro S G hS _ hG n hn
  have twoNeZero : (2 : ℚ⟦X⟧) ≠ 0 := by
    intro h
    have hc := congrArg (constantCoeff (R := ℚ)) h
    norm_num [map_ofNat] at hc
  have dTwo : d⁄dX ℚ (2 : ℚ⟦X⟧) = 0 := (d⁄dX ℚ).map_natCast 2
  have dThree : d⁄dX ℚ (3 : ℚ⟦X⟧) = 0 := (d⁄dX ℚ).map_natCast 3

  have hSd : S * d⁄dX ℚ S = -1 - 3 * X := by
    have hd := congrArg (fun f : ℚ⟦X⟧ => d⁄dX ℚ f) hS
    change d⁄dX ℚ (S ^ 2) = d⁄dX ℚ (1 - 2 * X - 3 * X ^ 2) at hd
    simp only [derivative_pow, map_sub, Derivation.map_one_eq_zero, Derivation.leibniz,
      smul_eq_mul, derivative_X, dTwo, dThree] at hd
    push_cast at hd
    apply mul_left_cancel₀ twoNeZero
    linear_combination hd
  have hQS : (1 - 2 * X - 3 * X ^ 2) * d⁄dX ℚ S = (-1 - 3 * X) * S := by
    linear_combination S * hSd - d⁄dX ℚ S * hS
  have hH : 2 * X ^ 2 * G = 1 - 2 * X + X ^ 2 + 2 * X ^ 3 - (1 - X) * S := by
    apply mul_left_cancel₀ twoNeZero
    linear_combination (-1 + X + S) * hG + (G - X) * hS
  have hHd : 4 * X * G + 2 * X ^ 2 * d⁄dX ℚ G =
      -2 + 2 * X + 6 * X ^ 2 + S - (1 - X) * d⁄dX ℚ S := by
    have hd := congrArg (fun f : ℚ⟦X⟧ => d⁄dX ℚ f) hH
    change d⁄dX ℚ (2 * X ^ 2 * G) =
      d⁄dX ℚ (1 - 2 * X + X ^ 2 + 2 * X ^ 3 - (1 - X) * S) at hd
    simp only [derivative_pow, map_add, map_sub, Derivation.map_one_eq_zero, Derivation.leibniz,
      smul_eq_mul, derivative_X, dTwo] at hd
    push_cast at hd
    linear_combination hd

  have ode : (1 - 3 * X - X ^ 2 + 3 * X ^ 3) * (X * d⁄dX ℚ G) +
      (2 - 4 * X - 2 * X ^ 2) * G = 2 - X - 5 * X ^ 2 - 3 * X ^ 3 + 3 * X ^ 4 := by
    apply mul_left_cancel₀ (mul_ne_zero twoNeZero (X_ne_zero (R := ℚ)))
    linear_combination (1 - X) * (1 - 2 * X - 3 * X ^ 2) * hHd +
      2 * (1 - 3 * X ^ 2) * hH - (1 - X) ^ 2 * hQS

  have odeG :
      euler G + 2 * G + X ^ 1 * (-3 * euler G - 4 * G) + X ^ 2 * (-1 * euler G - 2 * G) +
        X ^ 3 * (3 * euler G) =
      2 - X - 5 * X ^ 2 - 3 * X ^ 3 + 3 * X ^ 4 := by
    simp only [euler]
    linear_combination ode

  have hc := congrArg (coeff n) odeG
  have shift1 := coeff_shift n 1 (by omega)
  have shift2 := coeff_shift n 2 (by omega)
  have shift3 := coeff_shift n 3 (by omega)
  have hn0 : n ≠ 0 := by omega
  have hn1 : n ≠ 1 := by omega
  have hn2 : n ≠ 2 := by omega
  have hn3 : n ≠ 3 := by omega
  have hn4 : n ≠ 4 := by omega
  simp only [map_add, map_sub, shift1, shift2, shift3, map_neg, neg_mul, one_mul,
    ← map_ofNat C, coeff_C_mul, coeff_C, coeff_euler, coeff_X, coeff_X_pow, if_neg hn0,
    if_neg hn1, if_neg hn2, if_neg hn3, if_neg hn4, mul_zero, add_zero, sub_zero] at hc
  have cast1 : ((n - 1 : ℕ) : ℚ) = (n : ℚ) - 1 := by
    rw [Nat.cast_sub (by omega : 1 ≤ n), Nat.cast_one]
  have cast2 : ((n - 2 : ℕ) : ℚ) = (n : ℚ) - 2 := by
    rw [Nat.cast_sub (by omega : 2 ≤ n), Nat.cast_ofNat]
  have cast3 : ((n - 3 : ℕ) : ℚ) = (n : ℚ) - 3 := by
    rw [Nat.cast_sub (by omega : 3 ≤ n), Nat.cast_ofNat]
  rw [cast1, cast2, cast3] at hc
  linear_combination hc
