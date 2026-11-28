import OMAStatements.S_oeis_a172064

open PowerSeries

private theorem derivative_numeral (m : ℕ) [m.AtLeastTwo] :
    derivative ℚ (no_index (OfNat.ofNat m : ℚ⟦X⟧)) = 0 := by
  rw [← map_ofNat C m]
  exact derivative_C

private noncomputable def θ (f : ℚ⟦X⟧) : ℚ⟦X⟧ := X * derivative ℚ f

private theorem coeff_θ (f : ℚ⟦X⟧) (m : ℕ) :
    coeff m (θ f) = (m : ℚ) * coeff m f := by
  cases m with
  | zero => simp [θ]
  | succ m =>
    rw [θ, coeff_succ_X_mul, coeff_derivative, mul_comm]
    simp only [Nat.cast_add, Nat.cast_one]

private theorem coeff_sq_X_mul (f : ℚ⟦X⟧) (m : ℕ) :
    coeff (m + 2) (X ^ 2 * f) = coeff m f := by
  rw [pow_two, mul_assoc, coeff_succ_X_mul, coeff_succ_X_mul]

private theorem coeff_ofNat_mul (k : ℕ) [k.AtLeastTwo] (f : ℚ⟦X⟧) (m : ℕ) :
    coeff m ((no_index (OfNat.ofNat k : ℚ⟦X⟧)) * f) =
      (no_index (OfNat.ofNat k : ℚ)) * coeff m f := by
  rw [← map_ofNat C k, coeff_C_mul]

private theorem θ_two (f : ℚ⟦X⟧) :
    θ (θ f) = X * derivative ℚ f + X ^ 2 * derivative ℚ (derivative ℚ f) := by
  simp only [θ, Derivation.leibniz, derivative_X, smul_eq_mul]
  ring

private theorem θ_three (f : ℚ⟦X⟧) :
    θ (θ (θ f)) = X * derivative ℚ f + 3 * X ^ 2 * derivative ℚ (derivative ℚ f) +
      X ^ 3 * derivative ℚ (derivative ℚ (derivative ℚ f)) := by
  rw [θ_two, θ]
  simp only [pow_two, pow_three, map_add, Derivation.leibniz,
    derivative_X, derivative_one, smul_eq_mul]
  ring

private theorem generating_function_ode (S c G : ℚ⟦X⟧)
    (hSq : S ^ 2 = 1 - 4 * X)
    (hS0 : coeff 0 S = 1)
    (hc : 2 * X * c = 1 - S)
    (hG : G * (3 * S - 1 + 4 * X) = 2 * c ^ 7) :
    (154 * θ G + 64 * θ (θ G) + 6 * θ (θ (θ G))) +
      X * (-1792 * G - 1206 * θ G - 275 * θ (θ G) - 21 * θ (θ (θ G))) +
      X ^ 2 * (-1800 * G - 1030 * θ G - 194 * θ (θ G) - 12 * θ (θ (θ G))) = 0 := by
  have h2_ne : (2 : ℚ⟦X⟧) ≠ 0 := by
    rw [← map_ofNat C 2]
    intro h
    have := congrArg (coeff 0) h
    simp only [coeff_C, ↓reduceIte, map_zero] at this
    norm_num at this
  have h4_ne : (4 : ℚ⟦X⟧) ≠ 0 := by
    rw [← map_ofNat C 4]
    intro h
    have := congrArg (coeff 0) h
    simp only [coeff_C, ↓reduceIte, map_zero] at this
    norm_num at this
  have h2X_ne : (2 : ℚ⟦X⟧) * X ≠ 0 := by
    intro h
    have := congrArg (coeff 1) h
    rw [← map_ofNat C 2, coeff_C_mul, coeff_X, if_pos rfl, map_zero] at this
    norm_num at this
  have hS_ne : S ≠ 0 := by
    intro h
    rw [h, map_zero] at hS0
    norm_num at hS0
  have h1S_ne : (1 + S : ℚ⟦X⟧) ≠ 0 := by
    intro h
    have := congrArg (coeff 0) h
    simp only [map_add, coeff_one, ↓reduceIte, hS0, map_zero] at this
    norm_num at this
  have h3S_ne : (3 - S : ℚ⟦X⟧) ≠ 0 := by
    intro h
    have := congrArg (coeff 0) h
    rw [map_sub, ← map_ofNat C 3, coeff_C, if_pos rfl, hS0, map_zero] at this
    norm_num at this
  have h1Sc : (1 + S) * c = 2 := by
    apply mul_left_cancel₀ h2X_ne
    linear_combination (1 + S) * hc - hSq
  have hSderiv : S * derivative ℚ S = -2 := by
    have hd := congrArg (derivative ℚ) hSq
    simp [derivative_numeral, Derivation.leibniz, smul_eq_mul] at hd
    apply mul_left_cancel₀ h2_ne
    linear_combination hd
  have hcderiv : S * derivative ℚ c = c ^ 2 := by
    have hd := congrArg (derivative ℚ) h1Sc
    simp [derivative_numeral, Derivation.leibniz, smul_eq_mul] at hd
    apply mul_left_cancel₀ h2_ne
    linear_combination S * c * hd - c ^ 2 * hSderiv - S * derivative ℚ c * h1Sc
  have hGS : G * S * (3 - S) = 2 * c ^ 7 := by
    linear_combination hG - G * hSq
  let Q : ℚ⟦X⟧ := (1 + S) * (3 - S)
  let B : ℚ⟦X⟧ := S ^ 2 * Q
  let A1 : ℚ⟦X⟧ := 6 + 44 * S - 18 * S ^ 2
  let A2 : ℚ⟦X⟧ := 108 + 864 * S + 2024 * S ^ 2 - 1920 * S ^ 3 + 396 * S ^ 4
  let A3 : ℚ⟦X⟧ := 3240 + 28080 * S + 88056 * S ^ 2 + 70752 * S ^ 3 - 165864 * S ^ 4 + 74352 * S ^ 5 - 10296 * S ^ 6
  let G1 := derivative ℚ G
  let G2 := derivative ℚ G1
  let G3 := derivative ℚ G2
  have hB_ne : B ≠ 0 := mul_ne_zero (pow_ne_zero 2 hS_ne) (mul_ne_zero h1S_ne h3S_ne)
  have hG1 : B * G1 = A1 * G := by
    have hd := congrArg (derivative ℚ) hGS
    simp only [map_sub, derivative_numeral, Derivation.leibniz,
      Derivation.leibniz_pow, nsmul_eq_mul, smul_eq_mul, Nat.cast_ofNat] at hd
    norm_num at hd
    linear_combination S * (1 + S) * hd + 14 * (1 + S) * c ^ 6 * hcderiv +
      14 * c ^ 7 * h1Sc - 14 * hGS - G * (1 + S) * (3 - 2 * S) * hSderiv
  have hBderiv : derivative ℚ B = -12 - 12 * S + 8 * S ^ 2 := by
    have hd : derivative ℚ B = derivative ℚ (S ^ 2 * ((1 + S) * (3 - S))) := rfl
    simp only [map_add, map_sub, derivative_numeral, derivative_one, Derivation.leibniz,
      Derivation.leibniz_pow, nsmul_eq_mul, smul_eq_mul, Nat.cast_ofNat] at hd
    linear_combination hd + (6 + 6 * S - 4 * S ^ 2) * hSderiv
  have hA1deriv : S * derivative ℚ A1 = -88 + 72 * S := by
    have hd : derivative ℚ A1 = derivative ℚ (6 + 44 * S - 18 * S ^ 2) := rfl
    simp only [map_add, map_sub, derivative_numeral, Derivation.leibniz,
      Derivation.leibniz_pow, nsmul_eq_mul, smul_eq_mul, Nat.cast_ofNat] at hd
    linear_combination S * hd + (44 - 36 * S) * hSderiv
  have hG2 : B ^ 2 * G2 = A2 * G := by
    have hd := congrArg (derivative ℚ) hG1
    simp only [Derivation.leibniz, smul_eq_mul] at hd
    linear_combination B * hd + (A1 - derivative ℚ B) * hG1 +
      G * S * Q * hA1deriv - G * A1 * hBderiv
  have hA2deriv : S * derivative ℚ A2 = -1728 - 8096 * S + 11520 * S ^ 2 - 3168 * S ^ 3 := by
    have hd : derivative ℚ A2 = derivative ℚ (108 + 864 * S + 2024 * S ^ 2 - 1920 * S ^ 3 + 396 * S ^ 4) := rfl
    simp only [map_add, map_sub, derivative_numeral, Derivation.leibniz,
      Derivation.leibniz_pow, nsmul_eq_mul, smul_eq_mul, Nat.cast_ofNat] at hd
    linear_combination S * hd + (864 + 4048 * S - 5760 * S ^ 2 + 1584 * S ^ 3) * hSderiv
  have hG3 : B ^ 3 * G3 = A3 * G := by
    have hd := congrArg (derivative ℚ) hG2
    simp only [Derivation.leibniz, Derivation.leibniz_pow, nsmul_eq_mul, smul_eq_mul,
      Nat.cast_ofNat] at hd
    linear_combination B * hd + A2 * hG1 - 2 * derivative ℚ B * hG2 +
      G * S * Q * hA2deriv - 2 * G * A2 * hBderiv
  have h4X : (4 : ℚ⟦X⟧) * X = 1 - S ^ 2 := by linear_combination hSq
  have hP : (-1792 * X - 1800 * X ^ 2) * B ^ 3 + (224 * X - 1502 * X ^ 2 - 1236 * X ^ 3) * B ^ 2 * A1 +
      (82 * X ^ 2 - 338 * X ^ 3 - 230 * X ^ 4) * B * A2 + (6 * X ^ 3 - 21 * X ^ 4 - 12 * X ^ 5) * A3 = 0 := by
    apply mul_left_cancel₀ (pow_ne_zero 5 h4_ne)
    rw [mul_zero]
    have h4eq : (4 : ℚ⟦X⟧) ^ 5 * ((-1792 * X - 1800 * X ^ 2) * B ^ 3 + (224 * X - 1502 * X ^ 2 - 1236 * X ^ 3) * B ^ 2 * A1 +
        (82 * X ^ 2 - 338 * X ^ 3 - 230 * X ^ 4) * B * A2 + (6 * X ^ 3 - 21 * X ^ 4 - 12 * X ^ 5) * A3) =
        (-458752 * (4 * X) - 115200 * (4 * X) ^ 2) * B ^ 3 + (57344 * (4 * X) - 96128 * (4 * X) ^ 2 - 19776 * (4 * X) ^ 3) * B ^ 2 * A1 +
        (5248 * (4 * X) ^ 2 - 5408 * (4 * X) ^ 3 - 920 * (4 * X) ^ 4) * B * A2 + (96 * (4 * X) ^ 3 - 84 * (4 * X) ^ 4 - 12 * (4 * X) ^ 5) * A3 := by ring
    rw [h4eq, h4X]
    simp only [B, Q, A1, A2, A3]
    ring
  rw [θ_three, θ_two]
  dsimp only [θ]
  apply mul_left_cancel₀ (pow_ne_zero 3 hB_ne)
  rw [mul_zero]
  have hC : B ^ 3 * ((154 * (X * G1) + 64 * (X * G1 + X ^ 2 * G2) + 6 * (X * G1 + 3 * X ^ 2 * G2 + X ^ 3 * G3)) +
      X * (-1792 * G - 1206 * (X * G1) - 275 * (X * G1 + X ^ 2 * G2) - 21 * (X * G1 + 3 * X ^ 2 * G2 + X ^ 3 * G3)) +
      X ^ 2 * (-1800 * G - 1030 * (X * G1) - 194 * (X * G1 + X ^ 2 * G2) - 12 * (X * G1 + 3 * X ^ 2 * G2 + X ^ 3 * G3))) =
      ((-1792 * X - 1800 * X ^ 2) * B ^ 3 +
        (224 * X - 1502 * X ^ 2 - 1236 * X ^ 3) * B ^ 2 * A1 +
        (82 * X ^ 2 - 338 * X ^ 3 - 230 * X ^ 4) * B * A2 +
        (6 * X ^ 3 - 21 * X ^ 4 - 12 * X ^ 5) * A3) * G := by
    linear_combination (224 * X - 1502 * X ^ 2 - 1236 * X ^ 3) * B ^ 2 * hG1 +
      (82 * X ^ 2 - 338 * X ^ 3 - 230 * X ^ 4) * B * hG2 +
      (6 * X ^ 3 - 21 * X ^ 4 - 12 * X ^ 5) * hG3
  rw [hC, hP, zero_mul]

theorem OMA.solution : type_of% @OMA.S_oeis_a172064.main := by
  intro S c G hSq hS0 hc hG n hn
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 2 := ⟨n - 2, by omega⟩
  have hcoef := congrArg (coeff (m + 2)) (generating_function_ode S c G hSq hS0 hc hG)
  simp only [map_add, map_sub, map_neg, neg_mul, coeff_succ_X_mul, coeff_sq_X_mul,
    coeff_ofNat_mul, coeff_θ, map_zero] at hcoef
  simp only [show m + 2 - 1 = m + 1 by omega, show m + 2 - 2 = m by omega]
  push_cast at hcoef ⊢
  linear_combination hcoef
