import OMAStatements.S_oeis_a176605

/-!
Source: https://oeis.org/A176605

The quadratic generating function recorded by Michael Somos turns into a
cleared square equation for 1 - 2 X G. Differentiating that equation and
eliminating the square gives Mathar's recurrence by taking coefficients.
-/

namespace OMA.A176605

open OMA.S_oeis_a176605 PowerSeries

private theorem length_aList : ∀ n : ℕ, (aList n).length = n + 1
  | 0 => rfl
  | 1 => rfl
  | n + 2 => by
      rw [aList, List.length_append, length_aList (n + 1)]
      rfl

private theorem aList_getD {k n : ℕ} (h : k ≤ n) : (aList n).getD k 0 = a k := by
  induction n with
  | zero =>
      have hk : k = 0 := by omega
      subst k
      rfl
  | succ n ih =>
      by_cases hk : k = n + 1
      · subst k
        rfl
      have hkn : k ≤ n := by omega
      cases n with
      | zero =>
          have h0 : k = 0 := by omega
          subst k
          rfl
      | succ n =>
          rw [show n + 1 + 1 = n + 2 by omega, aList, List.getD_append]
          · exact ih hkn
          · rw [length_aList]
            omega

private theorem a_rec (n : ℕ) :
    a (n + 2) = (∑ k ∈ Finset.range (n + 2), a k * a (n + 1 - k)) + 1 := by
  unfold a
  rw [aList, List.getD_append_right _ _ _ _ (by rw [length_aList])]
  rw [length_aList, Nat.sub_self]
  change (∑ k ∈ Finset.range (n + 2),
      (aList (n + 1)).getD k 0 * (aList (n + 1)).getD (n + 1 - k) 0) + 1 = _
  change _ = (∑ k ∈ Finset.range (n + 2), a k * a (n + 1 - k)) + 1
  congr 1
  apply Finset.sum_congr rfl
  intro k hk
  rw [aList_getD (by have := Finset.mem_range.mp hk; omega), aList_getD (Nat.sub_le _ _)]

noncomputable def G : PowerSeries ℤ := PowerSeries.mk a

private theorem coeff_G_sq (n : ℕ) :
    coeff n (G ^ 2) = ∑ k ∈ Finset.range (n + 1), a k * a (n - k) := by
  rw [pow_two, coeff_mul, Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  simp only [G, coeff_mk]

/-- The defining quadratic recurrence determines this cleared generating function. -/
theorem generating_function :
    (1 - X) * (G - 1 - X * G ^ 2) = (X : PowerSeries ℤ) ^ 2 := by
  let U : PowerSeries ℤ := PowerSeries.mk (fun _ => 1)
  have hU : (1 - X) * U = 1 := by
    ext n
    rw [sub_mul, one_mul, map_sub]
    cases n with
    | zero => simp [U, coeff_zero_X_mul]
    | succ n => simp [U, coeff_one]
  have hG : G = 1 + X * G ^ 2 + X ^ 2 * U := by
    ext n
    simp only [map_add]
    rcases n with _ | _ | n
    · simp [G, U, coeff_zero_X_mul, coeff_X_pow_mul', a, aList]
    · simp [G, U, coeff_one, coeff_X_pow_mul', a, aList]
    · rw [coeff_succ_X_mul, coeff_one, if_neg (by omega), zero_add]
      have hX : coeff (n + 1 + 1) (X ^ 2 * U) = 1 := by
        rw [show n + 1 + 1 = n + 2 by omega, coeff_X_pow_mul]
        simp [U]
      rw [hX, coeff_G_sq]
      simpa only [G, coeff_mk, show n + 1 + 1 = n + 2 by omega] using a_rec n
  have hv : G - 1 - X * G ^ 2 = X ^ 2 * U := by linear_combination hG
  rw [hv]
  calc
    _ = (X : PowerSeries ℤ) ^ 2 * ((1 - X) * U) := by ring
    _ = _ := by rw [hU, mul_one]

end OMA.A176605

namespace OMA.A176605

open PowerSeries

/-- Differentiate a cleared quadratic equation and eliminate the square. -/
theorem quadratic_derivative (A B T : PowerSeries ℤ) (h : A * T ^ 2 = B) :
    2 * A * B * derivative ℤ T = (A * derivative ℤ B - derivative ℤ A * B) * T := by
  have hh := congrArg (fun P : PowerSeries ℤ => derivative ℤ P) h
  have hdiff : A * (2 * T * derivative ℤ T) + T ^ 2 * derivative ℤ A = derivative ℤ B := by
    simpa only [Derivation.leibniz, derivative_pow, smul_eq_mul, Nat.reduceSub,
      Nat.cast_ofNat, pow_one] using hh
  linear_combination A * T * hdiff - (2 * A * derivative ℤ T + derivative ℤ A * T) * h

noncomputable def euler (g : PowerSeries ℤ) : PowerSeries ℤ := g + X * derivative ℤ g

/-- The degree-four differential equation for the series of A176605. -/
theorem differential_eq (g : PowerSeries ℤ)
    (hg : (1 - X) * (g - 1 - X * g ^ 2) = (X : PowerSeries ℤ) ^ 2) :
    let L := euler g
    L + C (-6) * (X ^ 1 * L) + C 9 * (X ^ 2 * L) + C (-8) * (X ^ 3 * L) +
      C 4 * (X ^ 4 * L) + (C 2 * (X ^ 1 * g) + C (-4) * (X ^ 2 * g) +
        C 8 * (X ^ 3 * g) + C (-4) * (X ^ 4 * g)) =
      C 1 * X ^ 0 + C (-2) * X ^ 1 + C 4 * X ^ 2 + C (-2) * X ^ 3 := by
  let A := (1 : PowerSeries ℤ) - X
  let B := (1 : PowerSeries ℤ) - 5 * X + 4 * X ^ 2 - 4 * X ^ 3
  let T := (1 : PowerSeries ℤ) - 2 * (X * g)
  intro L
  have hT : A * T ^ 2 = B := by
    dsimp [A, B, T]
    linear_combination -4 * (X : PowerSeries ℤ) * hg
  have hD := quadratic_derivative A B T hT
  have hA' : derivative ℤ A = -1 := by simp [A, map_sub]
  have hd2 : derivative ℤ (2 : PowerSeries ℤ) = 0 := by
    simpa only [Nat.cast_ofNat] using (derivative ℤ).map_natCast 2
  have hd4 : derivative ℤ (4 : PowerSeries ℤ) = 0 := by
    simpa only [Nat.cast_ofNat] using (derivative ℤ).map_natCast 4
  have hd5 : derivative ℤ (5 : PowerSeries ℤ) = 0 := by
    simpa only [Nat.cast_ofNat] using (derivative ℤ).map_natCast 5
  have hB' : derivative ℤ B = -5 + 8 * X - 12 * X ^ 2 := by
    simp [B, map_sub, map_add, Derivation.leibniz, smul_eq_mul, hd4, hd5]
    ring
  have hT' : derivative ℤ T = -2 * L := by
    simp [T, L, euler, map_sub, Derivation.leibniz, smul_eq_mul, hd2]
    exact Or.inl (add_comm _ _)
  rw [hA', hB', hT'] at hD
  dsimp [A, B, T] at hD
  have hc : (4 : PowerSeries ℤ) ≠ 0 := by
    intro h
    have hf : (C (4 : ℤ) : PowerSeries ℤ) = 4 := map_ofNat C 4
    have hh := congrArg (constantCoeff (R := ℤ)) h
    rw [← hf, constantCoeff_C, map_zero] at hh
    omega
  apply mul_left_cancel₀ hc
  simp only [map_one, map_neg, map_ofNat, pow_zero, pow_one, mul_one]
  linear_combination -hD

end OMA.A176605

namespace OMA.A176605

open OMA.S_oeis_a176605 PowerSeries

private theorem coeff_euler (g : PowerSeries ℤ) (n : ℕ) :
    coeff n (euler g) = ((n : ℤ) + 1) * coeff n g := by
  unfold euler
  cases n with
  | zero => simp
  | succ n =>
      rw [map_add, coeff_succ_X_mul, coeff_derivative]
      push_cast
      ring

theorem linear_recurrence (n : ℕ) (hn : 4 ≤ n) :
    ((n : ℤ) + 1) * a n
      + 2 * (-3 * (n : ℤ) + 1) * a (n - 1)
      + (9 * (n : ℤ) - 13) * a (n - 2)
      + 8 * (-(n : ℤ) + 3) * a (n - 3)
      + 4 * ((n : ℤ) - 4) * a (n - 4) = 0 := by
  have h := congrArg (fun f : PowerSeries ℤ => coeff n f) (differential_eq G generating_function)
  have h1 : 1 ≤ n := by omega
  have h2 : 2 ≤ n := by omega
  have h3 : 3 ≤ n := by omega
  simp only [map_add, coeff_C_mul, coeff_X_pow_mul', coeff_X_pow,
    if_pos h1, if_pos h2, if_pos h3, if_pos hn, coeff_euler, G, coeff_mk,
    if_neg (by omega : n ≠ 0), if_neg (by omega : n ≠ 1),
    if_neg (by omega : n ≠ 2), if_neg (by omega : n ≠ 3),
    Int.natCast_sub h1, Int.natCast_sub h2, Int.natCast_sub h3, Int.natCast_sub hn,
    Nat.cast_ofNat, Nat.cast_one, mul_zero, add_zero] at h
  linear_combination h

end OMA.A176605

theorem OMA.solution : type_of% @OMA.S_oeis_a176605.main :=
  OMA.A176605.linear_recurrence
