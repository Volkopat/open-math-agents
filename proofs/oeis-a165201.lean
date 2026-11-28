import OMAStatements.S_oeis_a165201

open PowerSeries

private theorem derivative_numeral (m : ℕ) [m.AtLeastTwo] :
    derivative ℚ (no_index (OfNat.ofNat m : ℚ⟦X⟧)) = 0 := by
  rw [← map_ofNat C m]
  exact derivative_C

private theorem nz_ofNat (m : ℕ) [m.AtLeastTwo] : (no_index (OfNat.ofNat m : ℚ⟦X⟧)) ≠ 0 := by
  rw [← map_ofNat C m]
  intro h
  have hc := congrArg (fun f : ℚ⟦X⟧ => constantCoeff f) h
  change constantCoeff (C (m : ℚ)) = constantCoeff (0 : ℚ⟦X⟧) at hc
  simp at hc
  have : 2 ≤ m := Nat.AtLeastTwo.prop
  omega

private theorem nz_X : (X : ℚ⟦X⟧) ≠ 0 := by
  intro h
  have hc := congrArg (coeff 1) h
  simp at hc

private theorem nz_one_sub_4X : (1 - 4 * X : ℚ⟦X⟧) ≠ 0 := by
  intro h
  have hc := congrArg (fun f : ℚ⟦X⟧ => constantCoeff f) h
  simp at hc

private theorem generating_function_ode (S c G : ℚ⟦X⟧)
    (hSq : S ^ 2 = 1 - 4 * X)
    (hc : 2 * X * c = 1 - S)
    (hG : G * (1 - X * c ^ 3) = 1) :
    (X * derivative ℚ (derivative ℚ G)) -
      C 8 * (X ^ 2 * derivative ℚ (derivative ℚ G)) +
      C 15 * (X ^ 3 * derivative ℚ (derivative ℚ G)) +
      C 4 * (X ^ 4 * derivative ℚ (derivative ℚ G)) -
      C 2 * derivative ℚ G +
      C 6 * (X * derivative ℚ G) +
      C 6 * (X ^ 2 * derivative ℚ G) +
      C 10 * (X ^ 3 * derivative ℚ G) +
      C 2 * G +
      C 2 * (X * G) +
      C 2 * (X ^ 2 * G) = C 2 * X + C 2 * X ^ 2 := by
  have hTwo : (2 : ℚ⟦X⟧) ≠ 0 := nz_ofNat 2
  have hFour : (4 : ℚ⟦X⟧) ≠ 0 := nz_ofNat 4
  have hSqDerivative : 2 * S * derivative ℚ S = -4 := by
    have hd := congrArg (fun f : ℚ⟦X⟧ => derivative ℚ f) hSq
    simp [derivative_numeral, Derivation.leibniz, smul_eq_mul] at hd
    linear_combination hd
  have hRadicalODE : (1 - 4 * X) * derivative ℚ S = -2 * S := by
    apply mul_left_cancel₀ hTwo
    linear_combination S * hSqDerivative - 2 * derivative ℚ S * hSq
  have hS3 : S ^ 3 = (1 - 4 * X) * S := by
    rw [show S ^ 3 = S ^ 2 * S by ring, hSq]
  have h0a : ((-1 + 3 * X + 2 * X ^ 2) + (1 - X) * S) * G = 2 * X ^ 2 := by
    have hm := congrArg (fun f : ℚ⟦X⟧ => (2 * X) ^ 3 * f) hG
    have hr : (2 * X) ^ 3 * (G * (1 - X * c ^ 3)) =
        (8 * X ^ 3 - X * (1 - S) ^ 3) * G := by
      rw [show (2 * X) ^ 3 * (G * (1 - X * c ^ 3)) =
        (8 * X ^ 3 - X * (2 * X * c) ^ 3) * G by ring, hc]
    rw [hr] at hm
    have hcube : 8 * X ^ 3 - X * (1 - S) ^ 3 =
        4 * X * ((-1 + 3 * X + 2 * X ^ 2) + (1 - X) * S) := by
      ring_nf
      rw [hS3, hSq]
      ring
    rw [hcube] at hm
    apply mul_left_cancel₀ (mul_ne_zero hFour nz_X)
    linear_combination hm
  have h0 : (2 - 8 * X - 2 * X ^ 2) * G = (1 - 3 * X - 2 * X ^ 2) + (1 - X) * S := by
    have hm := congrArg (fun f : ℚ⟦X⟧ => ((-1 + 3 * X + 2 * X ^ 2) - (1 - X) * S) * f) h0a
    apply mul_left_cancel₀ (mul_ne_zero hTwo (pow_ne_zero 2 nz_X))
    linear_combination -hm - (1 - X) ^ 2 * G * hSq
  have hd0 := congrArg (fun f : ℚ⟦X⟧ => derivative ℚ f) h0
  simp [derivative_numeral, Derivation.leibniz, smul_eq_mul] at hd0
  have h1 : (-8 + 28 * X + 16 * X ^ 2) * G +
      (2 - 16 * X + 30 * X ^ 2 + 8 * X ^ 3) * derivative ℚ G =
      (-3 + 8 * X + 16 * X ^ 2) + (-3 + 6 * X) * S := by
    linear_combination (1 - 4 * X) * hd0 + (1 - X) * hRadicalODE
  have hd1 := congrArg (fun f : ℚ⟦X⟧ => derivative ℚ f) h1
  simp [derivative_numeral, Derivation.leibniz, smul_eq_mul] at hd1
  have h2 : (28 - 80 * X - 128 * X ^ 2) * G +
      (-24 + 184 * X - 312 * X ^ 2 - 160 * X ^ 3) * derivative ℚ G +
      (2 - 24 * X + 94 * X ^ 2 - 112 * X ^ 3 - 32 * X ^ 4) * derivative ℚ (derivative ℚ G) =
      (8 - 128 * X ^ 2) + (12 - 36 * X) * S := by
    linear_combination (1 - 4 * X) * hd1 + (-3 + 6 * X) * hRadicalODE
  rw [map_ofNat C 8, map_ofNat C 15, map_ofNat C 4, map_ofNat C 2,
    map_ofNat C 6, map_ofNat C 10]
  apply mul_left_cancel₀ (mul_ne_zero hTwo nz_one_sub_4X)
  linear_combination (-6 + 24 * X) * h0 + (-2 + 10 * X) * h1 + X * h2

private theorem coeff_X_pow_mul_zero (r m : ℕ) (p : ℚ⟦X⟧) (h : m < r) :
    coeff m (X ^ r * p) = 0 := by
  induction r generalizing m p with
  | zero => omega
  | succ r ih =>
    rw [pow_succ', mul_assoc]
    cases m with
    | zero => simp
    | succ m =>
      rw [coeff_succ_X_mul]
      exact ih m p (by omega)

private theorem coeff_k3_X_derivative2 (G : ℚ⟦X⟧) (k : ℕ) :
    coeff (k + 3) (X * derivative ℚ (derivative ℚ G)) =
      ((k : ℚ) + 3) * ((k : ℚ) + 4) * coeff (k + 4) G := by
  rw [coeff_succ_X_mul, coeff_derivative, coeff_derivative]
  push_cast
  ring

private theorem coeff_k3_X2_derivative2 (G : ℚ⟦X⟧) (k : ℕ) :
    coeff (k + 3) (X ^ 2 * derivative ℚ (derivative ℚ G)) =
      ((k : ℚ) + 2) * ((k : ℚ) + 3) * coeff (k + 3) G := by
  rw [show k + 3 = (k + 1) + 2 by omega, coeff_X_pow_mul, coeff_derivative, coeff_derivative]
  push_cast
  ring

private theorem coeff_k3_X3_derivative2 (G : ℚ⟦X⟧) (k : ℕ) :
    coeff (k + 3) (X ^ 3 * derivative ℚ (derivative ℚ G)) =
      ((k : ℚ) + 1) * ((k : ℚ) + 2) * coeff (k + 2) G := by
  rw [coeff_X_pow_mul, coeff_derivative, coeff_derivative]
  push_cast
  ring

private theorem coeff_k3_X4_derivative2 (G : ℚ⟦X⟧) (k : ℕ) :
    coeff (k + 3) (X ^ 4 * derivative ℚ (derivative ℚ G)) =
      (k : ℚ) * ((k : ℚ) + 1) * coeff (k + 1) G := by
  cases k with
  | zero => simp [coeff_X_pow_mul_zero 4 3 _ (by omega)]
  | succ k =>
    rw [show k + 1 + 3 = k + 4 by omega, coeff_X_pow_mul, coeff_derivative, coeff_derivative]
    push_cast
    ring

private theorem coeff_k3_derivative (G : ℚ⟦X⟧) (k : ℕ) :
    coeff (k + 3) (derivative ℚ G) = ((k : ℚ) + 4) * coeff (k + 4) G := by
  rw [coeff_derivative]
  push_cast
  ring

private theorem coeff_k3_X_derivative (G : ℚ⟦X⟧) (k : ℕ) :
    coeff (k + 3) (X * derivative ℚ G) = ((k : ℚ) + 3) * coeff (k + 3) G := by
  rw [coeff_succ_X_mul, coeff_derivative]
  push_cast
  ring

private theorem coeff_k3_X2_derivative (G : ℚ⟦X⟧) (k : ℕ) :
    coeff (k + 3) (X ^ 2 * derivative ℚ G) = ((k : ℚ) + 2) * coeff (k + 2) G := by
  rw [show k + 3 = (k + 1) + 2 by omega, coeff_X_pow_mul, coeff_derivative]
  push_cast
  ring

private theorem coeff_k3_X3_derivative (G : ℚ⟦X⟧) (k : ℕ) :
    coeff (k + 3) (X ^ 3 * derivative ℚ G) = ((k : ℚ) + 1) * coeff (k + 1) G := by
  rw [coeff_X_pow_mul, coeff_derivative]
  ring

private theorem coeff_k3_X2_mul (G : ℚ⟦X⟧) (k : ℕ) :
    coeff (k + 3) (X ^ 2 * G) = coeff (k + 1) G := by
  rw [show k + 3 = (k + 1) + 2 by omega, coeff_X_pow_mul]

theorem OMA.solution : type_of% @OMA.S_oeis_a165201.main := by
  intro S c G hSq _ hc hG n hn
  obtain ⟨k, rfl⟩ : ∃ k, n = k + 4 := ⟨n - 4, by omega⟩
  have hode := congrArg (coeff (k + 3)) (generating_function_ode S c G hSq hc hG)
  simp only [map_add, map_sub, coeff_C_mul, coeff_X, coeff_X_pow,
    show k + 3 ≠ 1 by omega, show k + 3 ≠ 2 by omega, if_false, mul_zero, add_zero] at hode
  rw [coeff_k3_X_derivative2, coeff_k3_X2_derivative2, coeff_k3_X3_derivative2,
    coeff_k3_X4_derivative2, coeff_k3_derivative, coeff_k3_X_derivative,
    coeff_k3_X2_derivative, coeff_k3_X3_derivative, coeff_succ_X_mul,
    coeff_k3_X2_mul] at hode
  simp only [show k + 4 - 1 = k + 3 by omega, show k + 4 - 2 = k + 2 by omega,
    show k + 4 - 3 = k + 1 by omega]
  push_cast at hode ⊢
  linear_combination hode
