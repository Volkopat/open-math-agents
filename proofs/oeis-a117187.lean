import OMAStatements.S_oeis_a117187

open PowerSeries

private theorem derivative_numeral (m : ℕ) [m.AtLeastTwo] :
    derivative ℚ (no_index (OfNat.ofNat m : ℚ⟦X⟧)) = 0 := by
  rw [← map_ofNat C m]
  exact derivative_C

private theorem numeral_ne_zero (m : ℕ) [m.AtLeastTwo] :
    (no_index (OfNat.ofNat m : ℚ⟦X⟧)) ≠ 0 := by
  rw [← map_ofNat C m]
  intro h
  have hc := congrArg (fun f : ℚ⟦X⟧ => constantCoeff f) h
  change constantCoeff (C (OfNat.ofNat m : ℚ)) = constantCoeff (0 : ℚ⟦X⟧) at hc
  rw [constantCoeff_C, map_zero] at hc
  exact (OfNat.ofNat_ne_zero m) hc

private theorem coeff_X_derivative (G : ℚ⟦X⟧) (k : ℕ) :
    coeff k (X * derivative ℚ G) = (k : ℚ) * coeff k G := by
  cases k with
  | zero => simp
  | succ k =>
    rw [coeff_succ_X_mul, coeff_derivative, mul_comm]
    simp only [Nat.cast_add, Nat.cast_one]

private theorem generating_function_ode (S c G : ℚ⟦X⟧)
    (hSq : S ^ 2 = 1 - 4 * X ^ 2) (hc : 2 * X ^ 2 * c = 1 - S)
    (hG : G * ((1 - X ^ 2 * c) * S) = (1 + X) * c) :
    (31 + 37 * X) * (1 - 4 * X ^ 2) * (X * derivative ℚ (X * derivative ℚ G)) +
      (112 + 98 * X - 820 * X ^ 2 - 836 * X ^ 3) * (X * derivative ℚ G) +
      (-48 - 95 * X - 1240 * X ^ 2 - 1080 * X ^ 3) * G = -48 := by
  have ha : X ^ 2 * G * S * (1 + S) = (1 + X) * (1 - S) := by
    linear_combination (2 * X ^ 2) * hG + (X ^ 2 * G * S + 1 + X) * hc
  have hb : 4 * X ^ 4 * G * S = 2 * (1 + X) * (1 - 2 * X ^ 2 - S) := by
    linear_combination (1 - S) * ha + (X ^ 2 * G * S + 1 + X) * hSq
  have h0 : 2 * X ^ 4 * (1 - 4 * X ^ 2) * G =
      (1 + X) * ((1 - 2 * X ^ 2) * S - (1 - 4 * X ^ 2)) := by
    apply mul_left_cancel₀ (numeral_ne_zero 2)
    linear_combination S * hb - (4 * X ^ 4 * G + 2 * (1 + X)) * hSq
  have hSqD : 2 * S * derivative ℚ S = -8 * X := by
    have hd := congrArg (fun f : ℚ⟦X⟧ => derivative ℚ f) hSq
    simp [derivative_numeral, Derivation.leibniz, Derivation.leibniz_pow, smul_eq_mul,
      nsmul_eq_mul] at hd
    linear_combination hd
  have hSD : (1 - 4 * X ^ 2) * derivative ℚ S = -4 * X * S := by
    apply mul_left_cancel₀ (numeral_ne_zero 2)
    linear_combination S * hSqD - 2 * derivative ℚ S * hSq
  have h1 : 2 * X ^ 4 * (1 - 4 * X ^ 2) ^ 2 * (X * derivative ℚ G) +
      2 * X ^ 4 * (1 - 4 * X ^ 2) * (4 - 24 * X ^ 2) * G =
      (1 - 4 * X ^ 2) * (-X + 8 * X ^ 2 + 12 * X ^ 3) +
        (X - 8 * X ^ 2 - 14 * X ^ 3 + 24 * X ^ 4 + 32 * X ^ 5) * S := by
    have hd := congrArg (fun f : ℚ⟦X⟧ => derivative ℚ f) h0
    simp [derivative_numeral, Derivation.leibniz, Derivation.leibniz_pow, smul_eq_mul,
      nsmul_eq_mul] at hd
    linear_combination (X * (1 - 4 * X ^ 2)) * hd + (X * (1 + X) * (1 - 2 * X ^ 2)) * hSD
  have h2 : (1 - 4 * X ^ 2) *
      (2 * X ^ 4 * (1 - 4 * X ^ 2) ^ 2 * (X * derivative ℚ (X * derivative ℚ G)) +
        2 * (4 * X ^ 4 - 48 * X ^ 6 + 128 * X ^ 8) * (X * derivative ℚ G) +
        2 * X ^ 4 * (1 - 4 * X ^ 2) * (4 - 24 * X ^ 2) * (X * derivative ℚ G) +
        2 * (16 * X ^ 4 - 240 * X ^ 6 + 768 * X ^ 8) * G) =
      (1 - 4 * X ^ 2) * (-X + 16 * X ^ 2 + 48 * X ^ 3 - 128 * X ^ 4 - 240 * X ^ 5) +
        ((1 - 4 * X ^ 2) * (X - 16 * X ^ 2 - 42 * X ^ 3 + 96 * X ^ 4 + 160 * X ^ 5) -
          4 * X ^ 2 * (X - 8 * X ^ 2 - 14 * X ^ 3 + 24 * X ^ 4 + 32 * X ^ 5)) * S := by
    have hd := congrArg (fun f : ℚ⟦X⟧ => derivative ℚ f) h1
    generalize hE : X * derivative ℚ G = E at hd ⊢
    simp [derivative_numeral, Derivation.leibniz, Derivation.leibniz_pow, smul_eq_mul,
      nsmul_eq_mul] at hd
    rw [← hE] at hd ⊢
    generalize derivative ℚ (X * derivative ℚ G) = E' at hd ⊢
    linear_combination (X * (1 - 4 * X ^ 2)) * hd +
      (X * (X - 8 * X ^ 2 - 14 * X ^ 3 + 24 * X ^ 4 + 32 * X ^ 5)) * hSD
  have hT : (1 - 4 * X ^ 2 : ℚ⟦X⟧) ≠ 0 := by
    intro h
    have hcc := congrArg (fun f : ℚ⟦X⟧ => constantCoeff f) h
    simp at hcc
  have hFac : (2 : ℚ⟦X⟧) * X ^ 4 * (1 - 4 * X ^ 2) ^ 2 ≠ 0 :=
    mul_ne_zero (mul_ne_zero (numeral_ne_zero 2) (pow_ne_zero _ X_ne_zero))
      (pow_ne_zero _ hT)
  apply mul_left_cancel₀ hFac
  linear_combination (31 + 37 * X) * h2 +
    (-136 - 198 * X + 916 * X ^ 2 + 1236 * X ^ 3) * h1 +
    (105 * X - 536 * X ^ 2 - 1516 * X ^ 3 + 3136 * X ^ 4 + 5568 * X ^ 5) * h0

theorem OMA.solution : type_of% @OMA.S_oeis_a117187.main := by
  intro S c G hSq _ hc hG n hn
  have hODE := generating_function_ode S c G hSq hc hG
  let E := X * derivative ℚ G
  let F := X * derivative ℚ E
  have hF : C 31 * F + C 112 * E - C 48 * G + C 37 * (X * F) + C 98 * (X * E) -
      C 95 * (X * G) - C 124 * (X ^ 2 * F) - C 820 * (X ^ 2 * E) - C 1240 * (X ^ 2 * G) -
      C 148 * (X ^ 3 * F) - C 836 * (X ^ 3 * E) - C 1080 * (X ^ 3 * G) = -C 48 := by
    dsimp only [F, E]
    simp only [map_ofNat]
    linear_combination hODE
  have coeff_E (k : ℕ) : coeff k E = (k : ℚ) * coeff k G := coeff_X_derivative G k
  have coeff_F (k : ℕ) : coeff k F = (k : ℚ) * ((k : ℚ) * coeff k G) := by
    rw [← coeff_E]
    exact coeff_X_derivative E k
  obtain ⟨k, rfl⟩ : ∃ k : ℕ, n = k + 3 := ⟨n - 3, by omega⟩
  have h := congrArg (fun P : ℚ⟦X⟧ => coeff (k + 3) P) hF
  change coeff (k + 3) _ = coeff (k + 3) _ at h
  have f2 : coeff (k + 3) (X ^ 2 * F) = coeff (k + 1) F := coeff_X_pow_mul F 2 (k + 1)
  have e2 : coeff (k + 3) (X ^ 2 * E) = coeff (k + 1) E := coeff_X_pow_mul E 2 (k + 1)
  have g2 : coeff (k + 3) (X ^ 2 * G) = coeff (k + 1) G := coeff_X_pow_mul G 2 (k + 1)
  simp only [map_add, map_sub, map_neg, coeff_C_mul, coeff_succ_X_mul, f2, e2, g2] at h
  simp only [coeff_X_pow_mul, coeff_E, coeff_F, coeff_C,
    if_neg (show k + 3 ≠ 0 by omega), neg_zero] at h
  rw [show k + 3 - 1 = k + 2 by omega, show k + 3 - 2 = k + 1 by omega,
    show k + 3 - 3 = k by omega]
  simp only [Nat.cast_add, Nat.cast_one, Nat.cast_ofNat] at h ⊢
  linear_combination h
