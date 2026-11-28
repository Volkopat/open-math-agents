import OMAStatements.S_oeis_a172025

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

private theorem nz_two_add_X : (2 + X : ℚ⟦X⟧) ≠ 0 := by
  intro h
  have hc := congrArg (fun f : ℚ⟦X⟧ => constantCoeff f) h
  simp at hc
  rw [← map_ofNat C 2] at hc
  change constantCoeff (C (2 : ℚ)) = constantCoeff (0 : ℚ⟦X⟧) at hc
  simp at hc

private theorem generating_function_ode (S c G : ℚ⟦X⟧)
    (hSq : S ^ 2 = 1 - 4 * X)
    (hc : 2 * X * c = 1 - S)
    (hG : G * (3 * S - 1 + 4 * X) = 2 * c ^ 3) :
    C 2 * (X * derivative ℚ (derivative ℚ G)) -
      C 7 * (X ^ 2 * derivative ℚ (derivative ℚ G)) -
      C 4 * (X ^ 3 * derivative ℚ (derivative ℚ G)) +
      C 8 * derivative ℚ G -
      C 38 * (X * derivative ℚ G) -
      C 30 * (X ^ 2 * derivative ℚ G) -
      C 32 * G -
      C 40 * (X * G) = 0 := by
  have hTwo : (2 : ℚ⟦X⟧) ≠ 0 := nz_ofNat 2
  have h16 : (16 : ℚ⟦X⟧) ≠ 0 := nz_ofNat 16
  have hSqDerivative : 2 * S * derivative ℚ S = -4 := by
    have hd := congrArg (fun f : ℚ⟦X⟧ => derivative ℚ f) hSq
    simp [derivative_numeral, Derivation.leibniz, smul_eq_mul] at hd
    linear_combination hd
  have hRadicalODE : (1 - 4 * X) * derivative ℚ S = -2 * S := by
    apply mul_left_cancel₀ hTwo
    linear_combination S * hSqDerivative - 2 * derivative ℚ S * hSq
  have hS3 : S ^ 3 = (1 - 4 * X) * S := by
    rw [show S ^ 3 = S ^ 2 * S by ring, hSq]
  have hS4 : S ^ 4 = (1 - 4 * X) ^ 2 := by
    rw [show S ^ 4 = (S ^ 2) ^ 2 by ring, hSq]
  have hpoly : 2 * (1 - S) ^ 3 * (3 * S + 1 - 4 * X) =
      16 * ((-1 + 4 * X) + (1 - 2 * X - 2 * X ^ 2) * S) := by
    ring_nf
    rw [hS4, hS3, hSq]
    ring
  have h0 : 2 * (1 - 4 * X) * (2 + X) * X ^ 3 * G =
      (-1 + 4 * X) + (1 - 2 * X - 2 * X ^ 2) * S := by
    apply mul_left_cancel₀ h16
    have hm := congrArg (fun f : ℚ⟦X⟧ => (2 * X) ^ 3 * (3 * S + 1 - 4 * X) * f) hG
    have hr : (2 * X) ^ 3 * (3 * S + 1 - 4 * X) * (2 * c ^ 3) =
        2 * (1 - S) ^ 3 * (3 * S + 1 - 4 * X) := by
      rw [show (2 * X) ^ 3 * (3 * S + 1 - 4 * X) * (2 * c ^ 3) =
        2 * (2 * X * c) ^ 3 * (3 * S + 1 - 4 * X) by ring, hc]
    rw [hr, hpoly] at hm
    linear_combination hm - 9 * (2 * X) ^ 3 * G * hSq
  have hd0 := congrArg (fun f : ℚ⟦X⟧ => derivative ℚ f) h0
  simp [derivative_numeral, Derivation.leibniz, smul_eq_mul] at hd0
  have h1 : (12 * X ^ 2 - 104 * X ^ 3 + 184 * X ^ 4 + 160 * X ^ 5) * G +
      (4 * X ^ 3 - 30 * X ^ 4 + 48 * X ^ 5 + 32 * X ^ 6) * derivative ℚ G =
      (4 - 16 * X) + (-4 + 8 * X + 20 * X ^ 2) * S := by
    linear_combination (1 - 4 * X) * hd0 + (1 - 2 * X - 2 * X ^ 2) * hRadicalODE
  have hd1 := congrArg (fun f : ℚ⟦X⟧ => derivative ℚ f) h1
  simp [derivative_numeral, Derivation.leibniz, smul_eq_mul] at hd1
  have h2 : (24 * X - 408 * X ^ 2 + 1984 * X ^ 3 - 2144 * X ^ 4 - 3200 * X ^ 5) * G +
      (24 * X ^ 2 - 320 * X ^ 3 + 1320 * X ^ 4 - 1344 * X ^ 5 - 1408 * X ^ 6) * derivative ℚ G +
      (4 * X ^ 3 - 46 * X ^ 4 + 168 * X ^ 5 - 160 * X ^ 6 - 128 * X ^ 7) *
        derivative ℚ (derivative ℚ G) =
      (-16 + 64 * X) + (16 - 8 * X - 200 * X ^ 2) * S := by
    linear_combination (1 - 4 * X) * hd1 + (-4 + 8 * X + 20 * X ^ 2) * hRadicalODE
  rw [map_ofNat C 2, map_ofNat C 7, map_ofNat C 4, map_ofNat C 8,
    map_ofNat C 38, map_ofNat C 30, map_ofNat C 32, map_ofNat C 40]
  have hM : (2 * (1 - 4 * X) ^ 3 * (2 + X) * X ^ 3 : ℚ⟦X⟧) ≠ 0 :=
    mul_ne_zero (mul_ne_zero (mul_ne_zero hTwo (pow_ne_zero 3 nz_one_sub_4X)) nz_two_add_X)
      (pow_ne_zero 3 nz_X)
  apply mul_left_cancel₀ hM
  linear_combination (-16 + 136 * X - 248 * X ^ 2 - 160 * X ^ 3) * h0 +
    (-4 + 42 * X - 90 * X ^ 2 - 56 * X ^ 3) * h1 +
    (2 * X - 7 * X ^ 2 - 4 * X ^ 3) * h2

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

private theorem coeff_succ_derivative (G : ℚ⟦X⟧) (k : ℕ) :
    coeff (k + 1) (derivative ℚ G) = ((k : ℚ) + 2) * coeff (k + 2) G := by
  rw [coeff_derivative]
  push_cast
  ring

private theorem coeff_succ_X_derivative (G : ℚ⟦X⟧) (k : ℕ) :
    coeff (k + 1) (X * derivative ℚ G) = ((k : ℚ) + 1) * coeff (k + 1) G := by
  rw [coeff_succ_X_mul, coeff_derivative]
  ring

private theorem coeff_succ_X2_derivative (G : ℚ⟦X⟧) (k : ℕ) :
    coeff (k + 1) (X ^ 2 * derivative ℚ G) = (k : ℚ) * coeff k G := by
  cases k with
  | zero => simp [coeff_X_pow_mul_zero 2 1 _ (by omega)]
  | succ k =>
    rw [show k + 1 + 1 = k + 2 by omega, coeff_X_pow_mul, coeff_derivative]
    push_cast
    ring

private theorem coeff_succ_X_derivative2 (G : ℚ⟦X⟧) (k : ℕ) :
    coeff (k + 1) (X * derivative ℚ (derivative ℚ G)) =
      ((k : ℚ) + 1) * ((k : ℚ) + 2) * coeff (k + 2) G := by
  rw [coeff_succ_X_mul, coeff_derivative, coeff_derivative]
  push_cast
  ring

private theorem coeff_succ_X2_derivative2 (G : ℚ⟦X⟧) (k : ℕ) :
    coeff (k + 1) (X ^ 2 * derivative ℚ (derivative ℚ G)) =
      (k : ℚ) * ((k : ℚ) + 1) * coeff (k + 1) G := by
  cases k with
  | zero => simp [coeff_X_pow_mul_zero 2 1 _ (by omega)]
  | succ k =>
    rw [show k + 1 + 1 = k + 2 by omega, coeff_X_pow_mul, coeff_derivative, coeff_derivative]
    push_cast
    ring

private theorem coeff_succ_X3_derivative2 (G : ℚ⟦X⟧) (k : ℕ) :
    coeff (k + 1) (X ^ 3 * derivative ℚ (derivative ℚ G)) =
      ((k : ℚ) - 1) * (k : ℚ) * coeff k G := by
  rcases k with _ | _ | k
  · simp [coeff_X_pow_mul_zero 3 1 _ (by omega)]
  · simp [coeff_X_pow_mul_zero 3 2 _ (by omega)]
  · rw [show k + 1 + 1 + 1 = k + 3 by omega, coeff_X_pow_mul, coeff_derivative, coeff_derivative]
    push_cast
    ring

theorem OMA.solution : type_of% @OMA.S_oeis_a172025.main := by
  intro S c G hSq _ hc hG n hn
  obtain ⟨k, rfl⟩ : ∃ k, n = k + 2 := ⟨n - 2, by omega⟩
  have hode := congrArg (coeff (k + 1)) (generating_function_ode S c G hSq hc hG)
  simp only [map_add, map_sub, map_zero, coeff_C_mul] at hode
  rw [coeff_succ_X_derivative2, coeff_succ_X2_derivative2, coeff_succ_X3_derivative2,
    coeff_succ_derivative, coeff_succ_X_derivative, coeff_succ_X2_derivative,
    coeff_succ_X_mul] at hode
  simp only [show k + 2 - 1 = k + 1 by omega, show k + 2 - 2 = k by omega]
  push_cast at hode ⊢
  linear_combination hode
