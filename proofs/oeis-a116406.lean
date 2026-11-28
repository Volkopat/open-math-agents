import OMAStatements.S_oeis_a116406

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

set_option maxHeartbeats 800000 in
theorem OMA.solution : type_of% @OMA.S_oeis_a116406.main := by
  intro S G hS hS0 hG n hn
  have twoNeZero : (2 : ℚ⟦X⟧) ≠ 0 := by
    intro h
    have hc := congrArg (constantCoeff (R := ℚ)) h
    norm_num [map_ofNat] at hc
  have d2 : d⁄dX ℚ (2 : ℚ⟦X⟧) = 0 := (d⁄dX ℚ).map_natCast 2
  have d4 : d⁄dX ℚ (4 : ℚ⟦X⟧) = 0 := (d⁄dX ℚ).map_natCast 4
  have d16 : d⁄dX ℚ (16 : ℚ⟦X⟧) = 0 := (d⁄dX ℚ).map_natCast 16
  let P : ℚ⟦X⟧ := 1 - 4 * X ^ 2
  let q : ℚ⟦X⟧ := -4 * X
  have pNeZero : P ≠ 0 := by
    change S ^ 2 = P at hS
    rw [← hS]
    apply pow_ne_zero
    intro h
    simp [h] at hS0
  have dP : d⁄dX ℚ P = -8 * X := by
    simp only [P, map_sub, Derivation.map_one_eq_zero, Derivation.leibniz,
      smul_eq_mul, derivative_pow, derivative_X, d4]
    ring
  have dq : d⁄dX ℚ q = -4 := by
    simp only [q, Derivation.leibniz, smul_eq_mul, map_neg, derivative_X, d4]
    ring
  have hSd : S * d⁄dX ℚ S = q := by
    have hd := congrArg (fun f : ℚ⟦X⟧ => d⁄dX ℚ f) hS
    change d⁄dX ℚ (S ^ 2) = d⁄dX ℚ P at hd
    simp only [derivative_pow, dP] at hd
    apply mul_left_cancel₀ twoNeZero
    dsimp only [q]
    linear_combination hd
  -- Clear the powers of P from the derivatives of the square root.
  have hS1 : P * d⁄dX ℚ S = q * S := by
    change S ^ 2 = P at hS
    linear_combination S * hSd - d⁄dX ℚ S * hS
  have hS2 : P ^ 2 * d⁄dX ℚ (d⁄dX ℚ S) = -4 * S := by
    have hd := congrArg (fun f : ℚ⟦X⟧ => d⁄dX ℚ f) hS1
    change d⁄dX ℚ (P * d⁄dX ℚ S) = d⁄dX ℚ (q * S) at hd
    simp only [Derivation.leibniz, smul_eq_mul, dP, dq] at hd
    dsimp only [P, q] at hd hS1 ⊢
    linear_combination (1 - 4 * X ^ 2) * hd - (-4 * X) * hS1

  -- Express a polynomial multiple of G in terms of S and differentiate twice.
  let T : ℚ⟦X⟧ := 2 * P
  let A : ℚ⟦X⟧ := 1 + X - 2 * X ^ 2
  let B : ℚ⟦X⟧ := 1 + X
  let T₁ : ℚ⟦X⟧ := -16 * X
  let A₁ : ℚ⟦X⟧ := 1 - 4 * X
  let B₁ : ℚ⟦X⟧ := 1
  let T₂ : ℚ⟦X⟧ := -16
  let A₂ : ℚ⟦X⟧ := -4
  let B₂ : ℚ⟦X⟧ := 0
  have h0 : T * G = A + B * S := by
    exact hG
  have h1 : T * d⁄dX ℚ G + T₁ * G = A₁ + B₁ * S + B * d⁄dX ℚ S := by
    have hd := congrArg (fun f : ℚ⟦X⟧ => d⁄dX ℚ f) h0
    change d⁄dX ℚ (T * G) = d⁄dX ℚ (A + B * S) at hd
    dsimp only [T, A, B, T₁, A₁, B₁] at hd ⊢
    simp only [map_add, map_sub, Derivation.map_one_eq_zero, Derivation.leibniz,
      smul_eq_mul, dP, derivative_pow, derivative_X, d2] at hd
    linear_combination hd
  have h2 : T * d⁄dX ℚ (d⁄dX ℚ G) + 2 * T₁ * d⁄dX ℚ G + T₂ * G =
      A₂ + B₂ * S + 2 * B₁ * d⁄dX ℚ S + B * d⁄dX ℚ (d⁄dX ℚ S) := by
    have hd := congrArg (fun f : ℚ⟦X⟧ => d⁄dX ℚ f) h1
    change d⁄dX ℚ (T * d⁄dX ℚ G + T₁ * G) = d⁄dX ℚ (A₁ + B₁ * S + B * d⁄dX ℚ S) at hd
    dsimp only [T, A₁, B, T₁, B₁, T₂, A₂, B₂] at hd ⊢
    simp only [map_add, map_sub, map_neg, Derivation.map_one_eq_zero,
      Derivation.leibniz, smul_eq_mul, dP, derivative_X, d2, d4, d16] at hd
    linear_combination hd

  let L₀ : ℚ⟦X⟧ := 2 * X
  let L₁ : ℚ⟦X⟧ := X * (-2 + 2 * X - 4 * X ^ 2 + 16 * X ^ 3)
  let L₂ : ℚ⟦X⟧ := X ^ 2 * (1 - 2 * X - 4 * X ^ 2 + 8 * X ^ 3)
  have ode : L₂ * d⁄dX ℚ (d⁄dX ℚ G) + L₁ * d⁄dX ℚ G + L₀ * G = 0 := by
    have tNeZero : T ≠ 0 := mul_ne_zero twoNeZero pNeZero
    apply mul_left_cancel₀ (mul_ne_zero (pow_ne_zero 3 tNeZero) (pow_ne_zero 2 pNeZero))
    let W₂ := T ^ 2 * L₂
    let W₁ := T * (T * L₁ - 2 * T₁ * L₂)
    let W₀ := T ^ 2 * L₀ - T * T₁ * L₁ + (2 * T₁ ^ 2 - T * T₂) * L₂
    dsimp only [W₂, W₁, W₀, L₀, L₁, L₂, T, T₁, T₂, A, A₁, A₂, B, B₁, B₂, P, q]
      at h0 h1 h2 hS1 hS2 ⊢
    linear_combination (norm := (dsimp only [W₂, W₁, W₀, T, T₁, T₂, L₀, L₁, L₂, B, B₁, P]; ring))
      (P ^ 2 * W₂) * h2 + (P ^ 2 * W₁) * h1 + (P ^ 2 * W₀) * h0 +
      (P * (W₁ * B + 2 * W₂ * B₁)) * hS1 + (W₂ * B) * hS2

  -- Euler differentiation multiplies each coefficient by its index.
  have odeEuler : -3 * euler G + euler (euler G) +
        X ^ 1 * (2 * G + 4 * euler G - 2 * euler (euler G)) +
        X ^ 2 * (-4 * euler (euler G)) +
        X ^ 3 * (8 * euler G + 8 * euler (euler G)) = 0 := by
    dsimp only [L₀, L₁, L₂] at ode
    simp only [euler, Derivation.leibniz, smul_eq_mul, derivative_X]
    linear_combination ode
  have hc := congrArg (coeff n) odeEuler
  have shift1 := coeff_shift n 1 (by omega)
  have cast1 : ((n - 1 : ℕ) : ℚ) = (n : ℚ) - 1 := by
    rw [Nat.cast_sub (by omega : 1 ≤ n), Nat.cast_one]
  have shift2 := coeff_shift n 2 (by omega)
  have cast2 : ((n - 2 : ℕ) : ℚ) = (n : ℚ) - 2 := by
    rw [Nat.cast_sub (by omega : 2 ≤ n), Nat.cast_ofNat]
  have shift3 := coeff_shift n 3 (by omega)
  have cast3 : ((n - 3 : ℕ) : ℚ) = (n : ℚ) - 3 := by
    rw [Nat.cast_sub (by omega : 3 ≤ n), Nat.cast_ofNat]
  simp only [map_add, map_sub, map_neg, map_zero, neg_mul, shift1, shift2, shift3,
    ← map_ofNat C, coeff_C_mul, coeff_euler] at hc
  rw [cast1, cast2, cast3] at hc
  linear_combination hc
