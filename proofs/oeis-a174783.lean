import OMAStatements.S_oeis_a174783

namespace OMA.A174783Proof

open PowerSeries

private lemma numeral_ne_zero (m : ℕ) [m.AtLeastTwo] (hm : (OfNat.ofNat m : ℚ) ≠ 0) :
    (OfNat.ofNat m : ℚ⟦X⟧) ≠ 0 := by
  rw [← map_ofNat C m, ← map_zero C]
  exact fun h => hm (C_injective h)

private lemma derivative_numeral (m : ℕ) [m.AtLeastTwo] :
    derivative ℚ (no_index (OfNat.ofNat m : ℚ⟦X⟧)) = 0 := by
  rw [← map_ofNat C m, derivative_C]

private lemma coeff_numeral_mul (m n : ℕ) [m.AtLeastTwo] (F : ℚ⟦X⟧) :
    coeff n ((no_index (OfNat.ofNat m : ℚ⟦X⟧)) * F) = (OfNat.ofNat m : ℚ) * coeff n F := by
  rw [← map_ofNat C m, coeff_C_mul]

private noncomputable def euler (F : ℚ⟦X⟧) : ℚ⟦X⟧ := X * derivative ℚ F

private lemma coeff_euler (F : ℚ⟦X⟧) (n : ℕ) :
    coeff n (euler F) = coeff n F * (n : ℚ) := by
  cases n with
  | zero => simp [euler]
  | succ n => rw [euler, coeff_succ_X_mul, coeff_derivative, Nat.cast_succ]

private lemma coeff_shift_one (F : ℚ⟦X⟧) (n : ℕ) (hn : 1 ≤ n) :
    coeff n (X * F) = coeff (n - 1) F := by
  rw [← pow_one (X : ℚ⟦X⟧), coeff_X_pow_mul', if_pos hn]

private lemma radical_ode (S : ℚ⟦X⟧) (hS : S ^ 2 = 1 - 4 * X ^ 2) :
    (1 - 4 * X ^ 2) * derivative ℚ S = (-4 * X) * S := by
  have hd := congrArg (derivative ℚ) hS
  simp [map_sub, Derivation.leibniz, smul_eq_mul, derivative_numeral] at hd
  apply mul_left_cancel₀ (numeral_ne_zero 2 (by norm_num))
  linear_combination S * hd - 2 * derivative ℚ S * hS

private lemma generating_ode (S G : ℚ⟦X⟧) (hS : S ^ 2 = 1 - 4 * X ^ 2)
    (hS0 : coeff 0 S = 1)
    (hG : G * (2 * (1 - X ^ 2) * S) = 1 + 2 * X - S) :
    (1 - 5 * X ^ 2 + 4 * X ^ 4) * euler G +
      (-2 * X - 2 * X ^ 2 + 2 * X ^ 3 + 8 * X ^ 4) * G = X := by
  let F : ℚ⟦X⟧ := 2 * (1 - X ^ 2) * G + 1
  have hFS : F * S = 1 + 2 * X := by
    dsimp [F]
    linear_combination hG
  have hFSd := congrArg (derivative ℚ) hFS
  simp [Derivation.leibniz, smul_eq_mul, derivative_numeral] at hFSd
  have hS_ne : S ≠ 0 := by
    intro h
    rw [h, map_zero] at hS0
    norm_num at hS0
  have hFode_mul : S * ((1 - 4 * X ^ 2) * derivative ℚ F - 2 * F) = 0 := by
    linear_combination (1 - 4 * X ^ 2) * hFSd - F * radical_ode S hS + (-2 + 4 * X) * hFS
  have hFode : (1 - 4 * X ^ 2) * derivative ℚ F = 2 * F := by
    have h := mul_left_cancel₀ hS_ne (by linear_combination hFode_mul : S * ((1 - 4 * X ^ 2) * derivative ℚ F - 2 * F) = S * 0)
    linear_combination h
  have hFd : derivative ℚ F = 2 * (1 - X ^ 2) * derivative ℚ G - 4 * X * G := by
    dsimp [F]
    simp [Derivation.leibniz, smul_eq_mul, derivative_numeral]
    ring
  rw [hFd] at hFode
  have hEq : (2 : ℚ⟦X⟧) * ((1 - 5 * X ^ 2 + 4 * X ^ 4) * euler G +
      (-2 * X - 2 * X ^ 2 + 2 * X ^ 3 + 8 * X ^ 4) * G) = (2 : ℚ⟦X⟧) * X := by
    unfold euler
    dsimp only [F] at hFode
    linear_combination X * hFode
  exact mul_left_cancel₀ (numeral_ne_zero 2 (by norm_num)) hEq

theorem recurrence (S G : ℚ⟦X⟧) (hS : S ^ 2 = 1 - 4 * X ^ 2) (hS0 : coeff 0 S = 1)
    (hG : G * (2 * (1 - X ^ 2) * S) = 1 + 2 * X - S) (n : ℕ) (hn : 4 ≤ n) :
    ((n : ℚ)) * coeff n G + (-2) * coeff (n - 1) G +
      (8 - 5 * (n : ℚ)) * coeff (n - 2) G + (2) * coeff (n - 3) G +
      (-8 + 4 * (n : ℚ)) * coeff (n - 4) G = 0 := by
  have hExpanded : euler G - 5 * (X ^ 2 * euler G) + 4 * (X ^ 4 * euler G) -
      2 * (X * G) - 2 * (X ^ 2 * G) + 2 * (X ^ 3 * G) + 8 * (X ^ 4 * G) = X := by
    linear_combination generating_ode S G hS hS0 hG
  have hc := congrArg (coeff n) hExpanded
  have hn1 : 1 ≤ n := by omega
  have hn2 : 2 ≤ n := by omega
  have hn3 : 3 ≤ n := by omega
  simp only [map_add, map_sub, coeff_numeral_mul, coeff_shift_one _ _ hn1,
    coeff_X_pow_mul', if_pos hn2, if_pos hn3, if_pos hn, coeff_euler, coeff_X,
    if_neg (show n ≠ 1 by omega)] at hc
  rw [Nat.cast_sub hn2, Nat.cast_sub hn] at hc
  push_cast at hc
  linear_combination hc

end OMA.A174783Proof

theorem OMA.solution : type_of% @OMA.S_oeis_a174783.main := by
  intro S G hS hS0 hG n hn
  exact OMA.A174783Proof.recurrence S G hS hS0 hG n hn
