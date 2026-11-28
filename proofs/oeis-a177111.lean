import OMAStatements.S_oeis_a177111

open PowerSeries

namespace OMA.S_oeis_a177111

noncomputable def A : PowerSeries ℤ := PowerSeries.mk a

lemma coeff_A (n : ℕ) : coeff n A = a n := by
  simp [A, coeff_mk]

lemma coeff_A_mul (n : ℕ) :
    coeff n (A * A) = ∑ p ∈ Finset.range (n + 1), a p * a (n - p) := by
  rw [coeff_mul, Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  simp [A, coeff_mk]

lemma coeff_X_mul (S : PowerSeries ℤ) (n : ℕ) :
    coeff n (X * S) = if 1 ≤ n then coeff (n - 1) S else 0 := by
  simpa using (coeff_X_pow_mul' S 1 n)

lemma coeff_X2_mul (S : PowerSeries ℤ) (n : ℕ) :
    coeff n (X * X * S) = if 2 ≤ n then coeff (n - 2) S else 0 := by
  simpa [pow_succ, mul_assoc] using (coeff_X_pow_mul' S 2 n)

lemma coeff_X3_mul (S : PowerSeries ℤ) (n : ℕ) :
    coeff n (X * X * X * S) = if 3 ≤ n then coeff (n - 3) S else 0 := by
  simpa [pow_succ, mul_assoc] using (coeff_X_pow_mul' S 3 n)

lemma alist_length : ∀ n, (aList n).length = n + 1 := by
  intro n
  induction n using Nat.twoStepInduction with
  | zero => simp [aList]
  | one => simp [aList]
  | more n ih0 ih1 => simp [aList, ih1]

lemma alist_getD_stable : ∀ n k, k ≤ n → (aList n).getD k 0 = a k := by
  intro n
  induction n using Nat.twoStepInduction with
  | zero =>
      intro k hk
      interval_cases k <;> simp [a, aList]
  | one =>
      intro k hk
      interval_cases k <;> simp [a, aList]
  | more n ih0 ih1 =>
      intro k hk
      by_cases hkn : k = n + 2
      · subst k
        simp [a, aList, alist_length]
      · have hk' : k ≤ n + 1 := by omega
        have h : (aList (n + 2)).getD k 0 = (aList (n + 1)).getD k 0 := by
          change (aList (n + 1) ++ [_]).getD k 0 = _
          rw [List.getD_append (h := by rw [alist_length]; omega)]
        rw [h, ih1 k hk']

lemma a_rec (n : ℕ) :
    a (n + 2) =
      (∑ p ∈ Finset.range (n + 2), a p * a (n + 1 - p)) - 2 * ((n : ℤ) + 2) := by
  have hnext : a (n + 2) =
      (∑ p ∈ Finset.range (n + 2),
        (aList (n + 1)).getD p 0 * (aList (n + 1)).getD (n + 1 - p) 0)
        - 2 * ((n : ℤ) + 2) := by
    change (aList (n + 2)).getD (n + 2) 0 = _
    simp only [aList]
    rw [List.getD_append_right
      (h := by have hlen := alist_length (n + 1); omega)]
    simp [alist_length]
  have hsum :
      (∑ p ∈ Finset.range (n + 2),
        (aList (n + 1)).getD p 0 * (aList (n + 1)).getD (n + 1 - p) 0)
        = ∑ p ∈ Finset.range (n + 2), a p * a (n + 1 - p) := by
    apply Finset.sum_congr rfl
    intro p hp
    have hp' : p ≤ n + 1 := by
      have := Finset.mem_range.mp hp
      omega
    have hq' : n + 1 - p ≤ n + 1 := by omega
    rw [alist_getD_stable (n + 1) p hp',
      alist_getD_stable (n + 1) (n + 1 - p) hq']
  rw [hnext, hsum]

lemma a_zero : a 0 = 1 := by simp [a, aList]

lemma a_one : a 1 = 1 := by simp [a, aList]

lemma a_two : a 2 = -2 := by
  rw [a_rec 0]
  norm_num [a_zero, a_one, Finset.sum_range_succ, Finset.sum_range_zero]

lemma a_three : a 3 = -9 := by
  rw [a_rec 1]
  norm_num [a_zero, a_one, a_two, Finset.sum_range_succ, Finset.sum_range_zero]

lemma coeff_A_sq_succ (n : ℕ) :
    coeff (n + 1) (A * A) = a (n + 2) + 2 * ((n : ℤ) + 2) := by
  rw [coeff_A_mul]
  have h := a_rec n
  linarith

lemma coeff_A_sq_zero : coeff 0 (A ^ 2) = 1 := by
  rw [pow_two, coeff_A_mul]
  simp [a_zero]

lemma coeff_A_sq_one : coeff 1 (A ^ 2) = 2 := by
  rw [pow_two, coeff_A_mul]
  norm_num [Finset.sum_range_succ, Finset.sum_range_zero, a_zero, a_one]

lemma coeff_A_sq_two : coeff 2 (A ^ 2) = -3 := by
  rw [pow_two, coeff_A_mul]
  norm_num [Finset.sum_range_succ, Finset.sum_range_zero, a_zero, a_one, a_two]

noncomputable def Q : PowerSeries ℤ :=
  X * (1 - X) ^ 2 * A ^ 2 - (1 - X) ^ 2 * A +
    (1 - 2 * X - 3 * X ^ 2 + 2 * X ^ 3)

noncomputable def P : PowerSeries ℤ := X * (1 - X) ^ 2
noncomputable def S : PowerSeries ℤ := (1 - X) ^ 2
noncomputable def E : PowerSeries ℤ := 1 - 2 * X - 3 * X ^ 2 + 2 * X ^ 3
noncomputable def dA : PowerSeries ℤ := PowerSeries.derivative ℤ A
noncomputable def U : PowerSeries ℤ :=
  X - 7 * X ^ 2 + 15 * X ^ 3 + 3 * X ^ 4 - 20 * X ^ 5 + 8 * X ^ 6
noncomputable def Ulin : PowerSeries ℤ :=
  (1 : ℤ) • X + (-7 : ℤ) • X ^ 2 + 15 • X ^ 3 + 3 • X ^ 4 - 20 • X ^ 5 + 8 • X ^ 6
noncomputable def V : PowerSeries ℤ := 1 - 5 * X + 9 * X ^ 2 - 15 * X ^ 3 + 2 * X ^ 4
noncomputable def W : PowerSeries ℤ := -1 + 3 * X + 9 * X ^ 2 - 11 * X ^ 3 + 4 * X ^ 4
noncomputable def R : PowerSeries ℤ :=
  1 - X - 9 * X ^ 2 - 15 * X ^ 3 + 48 * X ^ 4 - 24 * X ^ 5
noncomputable def FA : PowerSeries ℤ := 2 * P * A - S
noncomputable def FX : PowerSeries ℤ :=
  PowerSeries.derivative ℤ P * A ^ 2
    - PowerSeries.derivative ℤ S * A
    + PowerSeries.derivative ℤ E

lemma q_identity : Q = 0 := by
  ext n
  rw [show Q = X ^ 1 * A ^ 2 - (X ^ 2 * A ^ 2 + X ^ 2 * A ^ 2) + X ^ 3 * A ^ 2 -
      A + (X * A + X * A) - X ^ 2 * A +
      (1 - X - X - X ^ 2 - X ^ 2 - X ^ 2 + X ^ 3 + X ^ 3) by
    dsimp [Q]
    ring]
  simp [coeff_X_pow_mul', coeff_X_mul, coeff_X]
  by_cases hn : n < 4
  · interval_cases n
    · simp [coeff_A, a_zero]
    · norm_num [coeff_A, coeff_A_sq_zero, a_zero, a_one, coeff_X]
    · norm_num [coeff_A, coeff_A_sq_zero, coeff_A_sq_one, a_zero, a_one, a_two,
        coeff_X]
    · norm_num [coeff_A, coeff_A_sq_zero, coeff_A_sq_one, coeff_A_sq_two,
        a_zero, a_one, a_two, a_three, coeff_X]
  · have hn4 : 4 ≤ n := by omega
    obtain ⟨k, hk⟩ : ∃ k, n = k + 4 := ⟨n - 4, by omega⟩
    rw [hk]
    have h1 : 1 ≤ k + 4 := by omega
    have h2 : 2 ≤ k + 4 := by omega
    have h3 : 3 ≤ k + 4 := by omega
    have h0 : k + 4 ≠ 0 := by omega
    have h01 : k + 4 ≠ 1 := by omega
    have h02 : k + 4 ≠ 2 := by omega
    have h03 : k + 4 ≠ 3 := by omega
    have hs1 : k + 4 - 1 = k + 3 := by omega
    have hs2 : k + 4 - 2 = k + 2 := by omega
    have hs3 : k + 4 - 3 = k + 1 := by omega
    simp [h1, h2, h3, h01, h02, h03, hs1, hs2, hs3]
    rw [pow_two, coeff_A_sq_succ (k + 2), coeff_A_sq_succ (k + 1),
      coeff_A_sq_succ k]
    simp [coeff_A, coeff_X, h01]
    ring

lemma derivative_X : PowerSeries.derivative ℤ (X : PowerSeries ℤ) = 1 := by
  ext n
  rw [PowerSeries.coeff_derivative]
  cases n <;> simp [PowerSeries.coeff_X, PowerSeries.coeff_one]

lemma derivative_one : PowerSeries.derivative ℤ (1 : PowerSeries ℤ) = 0 := by
  ext n
  rw [PowerSeries.coeff_derivative]
  cases n <;> simp [PowerSeries.coeff_one]

lemma q_derivative : PowerSeries.derivative ℤ Q = 0 := by
  have h := congrArg (PowerSeries.derivative ℤ) q_identity
  simpa using h

lemma derivative_one_sub_X :
    PowerSeries.derivative ℤ (1 - X : PowerSeries ℤ) = -1 := by
  simp [sub_eq_add_neg, Derivation.map_add, derivative_one, derivative_X]

lemma derivative_S :
    PowerSeries.derivative ℤ S = -2 * (1 - X : PowerSeries ℤ) := by
  rw [show S = (1 - X : PowerSeries ℤ) * (1 - X) by simp [S, pow_two]]
  rw [Derivation.leibniz, derivative_one_sub_X]
  ring

lemma derivative_P :
    PowerSeries.derivative ℤ P =
      (1 - X : PowerSeries ℤ) ^ 2 - 2 * X * (1 - X) := by
  rw [show P = (X : PowerSeries ℤ) * S by rfl, Derivation.leibniz,
    derivative_X, derivative_S]
  simp [smul_eq_mul, S]
  ring

lemma derivative_int (z : ℤ) :
    PowerSeries.derivative ℤ (z : PowerSeries ℤ) = 0 := by
  have h := Derivation.map_smul (PowerSeries.derivative ℤ) z (1 : PowerSeries ℤ)
  simpa [derivative_one] using h

lemma derivative_nat (n : ℕ) :
    PowerSeries.derivative ℤ (n : PowerSeries ℤ) = 0 := by
  induction n with
  | zero => simp
  | succ n ih =>
      rw [Nat.cast_succ, Derivation.map_add]
      simp [ih, derivative_one]

lemma derivative_two : PowerSeries.derivative ℤ (2 : PowerSeries ℤ) = 0 := by
  simpa using derivative_int 2

lemma derivative_three : PowerSeries.derivative ℤ (3 : PowerSeries ℤ) = 0 := by
  simpa using derivative_int 3

lemma derivative_E :
    PowerSeries.derivative ℤ E = -2 - 6 * X + 6 * X ^ 2 := by
  dsimp [E]
  simp [Derivation.map_add, Derivation.leibniz, derivative_X, derivative_one,
    derivative_two, derivative_three]
  ring

lemma derivative_Q_form :
    PowerSeries.derivative ℤ Q =
      (2 * P * A - S) * dA
        + PowerSeries.derivative ℤ P * A ^ 2
        - PowerSeries.derivative ℤ S * A
        + PowerSeries.derivative ℤ E := by
  rw [show Q = P * A ^ 2 - S * A + E by
    dsimp [Q, P, S, E]]
  simp only [sub_eq_add_neg, Derivation.map_add, Derivation.leibniz, pow_two]
  simp [dA, smul_eq_mul]
  ring

lemma elimination :
    (V * A + W) * FA - U * FX = R * Q := by
  rw [show FA = 2 * P * A - S by rfl, show FX =
    PowerSeries.derivative ℤ P * A ^ 2 - PowerSeries.derivative ℤ S * A
      + PowerSeries.derivative ℤ E by rfl]
  rw [derivative_P, derivative_S, derivative_E]
  dsimp [U, V, W, R, Q, P, S, E]
  ring

lemma FA_ne_zero : FA ≠ 0 := by
  intro h
  have h0 := congrArg PowerSeries.constantCoeff h
  norm_num [FA, P, S] at h0

lemma ode_identity : U * dA + V * A + W = 0 := by
  have hd := q_derivative
  rw [derivative_Q_form] at hd
  have hfx : FX = -FA * dA := by
    dsimp [FX, FA] at hd ⊢
    linear_combination hd
  have hm : FA * (U * dA + V * A + W) = 0 := by
    calc
      FA * (U * dA + V * A + W) =
          (V * A + W) * FA - U * FX := by rw [hfx]; ring
      _ = R * Q := elimination
      _ = 0 := by rw [q_identity]; simp
  rcases mul_eq_zero.mp hm with hfa | hode
  · exact (FA_ne_zero hfa).elim
  · exact hode

lemma coeff_Ulin_dA (n : ℕ) :
    coeff n (Ulin * dA) =
      (if 1 ≤ n then coeff (n - 1) dA else 0)
        - 7 * (if 2 ≤ n then coeff (n - 2) dA else 0)
        + 15 * (if 3 ≤ n then coeff (n - 3) dA else 0)
        + 3 * (if 4 ≤ n then coeff (n - 4) dA else 0)
        - 20 * (if 5 ≤ n then coeff (n - 5) dA else 0)
        + 8 * (if 6 ≤ n then coeff (n - 6) dA else 0) := by
  have h (k : ℕ) :
      coeff n (X ^ k * dA) = if k ≤ n then coeff (n - k) dA else 0 := by
    simpa using (coeff_X_pow_mul' dA k n)
  have h1 : coeff n (X * dA) = if 1 ≤ n then coeff (n - 1) dA else 0 := by
    simpa using h 1
  have h2 : coeff n (X ^ 2 * dA) = if 2 ≤ n then coeff (n - 2) dA else 0 := by
    simpa using h 2
  have h3 : coeff n (X ^ 3 * dA) = if 3 ≤ n then coeff (n - 3) dA else 0 := by
    simpa using h 3
  have h4 : coeff n (X ^ 4 * dA) = if 4 ≤ n then coeff (n - 4) dA else 0 := by
    simpa using h 4
  have h5 : coeff n (X ^ 5 * dA) = if 5 ≤ n then coeff (n - 5) dA else 0 := by
    simpa using h 5
  have h6 : coeff n (X ^ 6 * dA) = if 6 ≤ n then coeff (n - 6) dA else 0 := by
    simpa using h 6
  have h7 : coeff n (7 * (X ^ 2 * dA)) = 7 * coeff n (X ^ 2 * dA) := by
    change coeff n (PowerSeries.C 7 * (X ^ 2 * dA)) = _
    rw [PowerSeries.coeff_C_mul]
  have h15 : coeff n (15 * (X ^ 3 * dA)) = 15 * coeff n (X ^ 3 * dA) := by
    change coeff n (PowerSeries.C 15 * (X ^ 3 * dA)) = _
    rw [PowerSeries.coeff_C_mul]
  have h3' : coeff n (3 * (X ^ 4 * dA)) = 3 * coeff n (X ^ 4 * dA) := by
    change coeff n (PowerSeries.C 3 * (X ^ 4 * dA)) = _
    rw [PowerSeries.coeff_C_mul]
  have h20 : coeff n (20 * (X ^ 5 * dA)) = 20 * coeff n (X ^ 5 * dA) := by
    change coeff n (PowerSeries.C 20 * (X ^ 5 * dA)) = _
    rw [PowerSeries.coeff_C_mul]
  have h8 : coeff n (8 * (X ^ 6 * dA)) = 8 * coeff n (X ^ 6 * dA) := by
    change coeff n (PowerSeries.C 8 * (X ^ 6 * dA)) = _
    rw [PowerSeries.coeff_C_mul]
  simp [Ulin, add_mul, sub_mul, mul_assoc, smul_mul_assoc,
    PowerSeries.coeff_smul, coeff_X_pow_mul', h1, h2, h3, h4, h5, h6, h7, h15,
    h3', h20, h8]
  ring

lemma coeff_dA (n : ℕ) : coeff n dA = (n + 1 : ℤ) * a (n + 1) := by
  change coeff n (PowerSeries.derivative ℤ A) = _
  rw [PowerSeries.coeff_derivative, coeff_A]
  ring

lemma U_eq_Ulin : U = Ulin := by
  dsimp [U, Ulin]
  ring

end OMA.S_oeis_a177111

open OMA.S_oeis_a177111

theorem OMA.solution : type_of% @OMA.S_oeis_a177111.main := by
  intro n hn
  have h := congrArg (coeff n) ode_identity
  rw [U_eq_Ulin] at h
  have hV :
      coeff n (V * A) =
        coeff n A - 5 * coeff (n - 1) A + 9 * coeff (n - 2) A
          - 15 * coeff (n - 3) A + 2 * coeff (n - 4) A := by
    have h5 : coeff n (5 * (X * A)) = 5 * coeff (n - 1) A := by
      change coeff n (PowerSeries.C 5 * (X * A)) = _
      rw [PowerSeries.coeff_C_mul, coeff_X_mul]
      have hone : 1 ≤ n := by omega
      simp [hone]
    have h9 : coeff n (9 * (X ^ 2 * A)) = 9 * coeff (n - 2) A := by
      change coeff n (PowerSeries.C 9 * (X ^ 2 * A)) = _
      rw [PowerSeries.coeff_C_mul, coeff_X_pow_mul']
      have htwo : 2 ≤ n := by omega
      simp [htwo]
    have h15 : coeff n (15 * (X ^ 3 * A)) = 15 * coeff (n - 3) A := by
      change coeff n (PowerSeries.C 15 * (X ^ 3 * A)) = _
      rw [PowerSeries.coeff_C_mul, coeff_X_pow_mul']
      have hthree : 3 ≤ n := by omega
      simp [hthree]
    have h2 : coeff n (2 * (X ^ 4 * A)) = 2 * coeff (n - 4) A := by
      change coeff n (PowerSeries.C 2 * (X ^ 4 * A)) = _
      rw [PowerSeries.coeff_C_mul, coeff_X_pow_mul']
      have hfour : 4 ≤ n := by omega
      simp [hfour]
    rw [show V * A = A - 5 * (X * A) + 9 * (X ^ 2 * A) -
      15 * (X ^ 3 * A) + 2 * (X ^ 4 * A) by dsimp [V]; ring]
    simp only [map_add, map_sub]
    rw [h5, h9, h15, h2]
  have hW :
      coeff n W = 0 := by
    have hc : coeff n (-1 : PowerSeries ℤ) = 0 := by
      have hn0 : n ≠ 0 := by omega
      simp [PowerSeries.coeff_one, hn0]
    have hx (k : ℕ) (hk : k ≤ 4) :
        coeff n ((X : PowerSeries ℤ) ^ k) = 0 := by
      rw [← mul_one ((X : PowerSeries ℤ) ^ k), coeff_X_pow_mul']
      have hkn : k ≤ n := by omega
      simp [hkn]
      omega
    have h3 : coeff n ((3 : PowerSeries ℤ) * X) = 0 := by
      change coeff n (PowerSeries.C 3 * (X : PowerSeries ℤ)) = 0
      rw [PowerSeries.coeff_C_mul]
      simpa using hx 1 (by omega)
    have h9 : coeff n ((9 : PowerSeries ℤ) * X ^ 2) = 0 := by
      change coeff n (PowerSeries.C 9 * (X : PowerSeries ℤ) ^ 2) = 0
      rw [PowerSeries.coeff_C_mul]
      simpa using hx 2 (by omega)
    have h11 : coeff n ((11 : PowerSeries ℤ) * X ^ 3) = 0 := by
      change coeff n (PowerSeries.C 11 * (X : PowerSeries ℤ) ^ 3) = 0
      rw [PowerSeries.coeff_C_mul]
      simpa using hx 3 (by omega)
    have h4 : coeff n ((4 : PowerSeries ℤ) * X ^ 4) = 0 := by
      change coeff n (PowerSeries.C 4 * (X : PowerSeries ℤ) ^ 4) = 0
      rw [PowerSeries.coeff_C_mul]
      simpa using hx 4 (by omega)
    dsimp [W]
    simp only [map_add, map_sub]
    rw [hc, h3, h9, h11, h4]
    ring
  simp only [map_add, map_sub] at h
  rw [hV, hW, coeff_Ulin_dA, coeff_dA, coeff_A] at h
  simp [coeff_dA, coeff_A, hn] at h
  norm_num at h
  have h1 : 1 ≤ n := by omega
  have h2 : 2 ≤ n := by omega
  have h3 : 3 ≤ n := by omega
  have h4 : 4 ≤ n := by omega
  have h5 : 5 ≤ n := hn
  have e1 : 1 + (n - 1) = n := by omega
  have e2 : 1 + (n - 2) = n - 1 := by omega
  have e3 : 1 + (n - 3) = n - 2 := by omega
  have e4 : 1 + (n - 4) = n - 3 := by omega
  have e5 : 1 + (n - 5) = n - 4 := by omega
  by_cases hn6 : 6 ≤ n
  · have e6 : 1 + (n - 6) = n - 5 := by omega
    have f2 : n - 2 + 1 = n - 1 := by omega
    have f3 : n - 3 + 1 = n - 2 := by omega
    have f4 : n - 4 + 1 = n - 3 := by omega
    have f5 : n - 5 + 1 = n - 4 := by omega
    have f6 : n - 6 + 1 = n - 5 := by omega
    simp [h1, h2, h3, h4, h5, hn6] at h
    rw [f2, f3, f4, f5, f6] at h
    ring_nf at h
    linarith
  · have hn5 : n = 5 := by omega
    subst n
    norm_num at h ⊢
    linarith

