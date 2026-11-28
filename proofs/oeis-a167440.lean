import OMAStatements.S_oeis_a167440

open Polynomial in
theorem OMA.aux_T5 :
    Chebyshev.T ℚ 5 = 16 * X ^ 5 - 20 * X ^ 3 + 5 * X := by
  have h3 : Chebyshev.T ℚ ((1 : ℤ) + 2) =
      2 * X * Chebyshev.T ℚ ((1 : ℤ) + 1) - Chebyshev.T ℚ 1 := Chebyshev.T_add_two ℚ 1
  have h4 : Chebyshev.T ℚ ((2 : ℤ) + 2) =
      2 * X * Chebyshev.T ℚ ((2 : ℤ) + 1) - Chebyshev.T ℚ 2 := Chebyshev.T_add_two ℚ 2
  have h5 : Chebyshev.T ℚ ((3 : ℤ) + 2) =
      2 * X * Chebyshev.T ℚ ((3 : ℤ) + 1) - Chebyshev.T ℚ 3 := Chebyshev.T_add_two ℚ 3
  have e2 : ((1 : ℤ) + 1) = 2 := by norm_num
  have e3 : ((1 : ℤ) + 2) = 3 := by norm_num
  have e3' : ((2 : ℤ) + 1) = 3 := by norm_num
  have e4 : ((2 : ℤ) + 2) = 4 := by norm_num
  have e4' : ((3 : ℤ) + 1) = 4 := by norm_num
  have e5 : ((3 : ℤ) + 2) = 5 := by norm_num
  rw [e3, e2, Chebyshev.T_two, Chebyshev.T_one] at h3
  rw [e4, e3', h3, Chebyshev.T_two] at h4
  rw [e5, e4', h4, h3] at h5
  rw [h5]
  ring

theorem OMA.aux_evalT5 (x : ℚ) :
    (Polynomial.Chebyshev.T ℚ 5).eval x = 16 * x ^ 5 - 20 * x ^ 3 + 5 * x := by
  rw [OMA.aux_T5]
  simp

theorem OMA.aux_closed (n : ℕ) (hn : 1 ≤ n) :
    OMA.S_oeis_a167440.a n = 2 ^ n * (5 - 5 * 4 ^ n + 16 ^ n) := by
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
  unfold OMA.S_oeis_a167440.a OMA.S_oeis_a167440.gegenbauerC
  simp only [Nat.add_sub_cancel, Nat.cast_ofNat]
  rw [OMA.aux_evalT5]
  have h4 : (4 : ℚ) ^ m = (2 ^ m) ^ 2 := by
    rw [← pow_mul, mul_comm, pow_mul]; norm_num
  have h16 : (16 : ℚ) ^ m = (2 ^ m) ^ 4 := by
    rw [← pow_mul, mul_comm, pow_mul]; norm_num
  rw [pow_succ (2 : ℚ) m, pow_succ (4 : ℚ) m, pow_succ (16 : ℚ) m, h4, h16]
  ring

theorem OMA.aux_rec (n : ℕ) (hn : 4 ≤ n) :
    OMA.S_oeis_a167440.a n = 42 * OMA.S_oeis_a167440.a (n - 1)
      - 336 * OMA.S_oeis_a167440.a (n - 2) + 512 * OMA.S_oeis_a167440.a (n - 3) := by
  obtain ⟨k, rfl⟩ : ∃ k, n = k + 4 := ⟨n - 4, by omega⟩
  have e1 : k + 4 - 1 = k + 3 := by omega
  have e2 : k + 4 - 2 = k + 2 := by omega
  have e3 : k + 4 - 3 = k + 1 := by omega
  rw [e1, e2, e3, OMA.aux_closed (k + 4) (by omega), OMA.aux_closed (k + 3) (by omega),
    OMA.aux_closed (k + 2) (by omega), OMA.aux_closed (k + 1) (by omega)]
  ring

open PowerSeries in
theorem OMA.aux_keyD (g : ℕ → ℚ) (n : ℕ) :
    coeff n (mk g * ((2 * X - 1) * (8 * X - 1) * (32 * X - 1))) =
      512 * (if 3 ≤ n then g (n - 3) else 0) - 336 * (if 2 ≤ n then g (n - 2) else 0)
        + 42 * (if 1 ≤ n then g (n - 1) else 0) - g n := by
  have hD : ((2 * X - 1) * (8 * X - 1) * (32 * X - 1) : PowerSeries ℚ) =
      C 512 * X ^ 3 - C 336 * X ^ 2 + C 42 * X ^ 1 - 1 := by
    simp only [map_ofNat]; ring
  have hM : mk g * (C 512 * X ^ 3 - C 336 * X ^ 2 + C 42 * X ^ 1 - 1) =
      C 512 * (mk g * X ^ 3) - C 336 * (mk g * X ^ 2) + C 42 * (mk g * X ^ 1) - mk g := by
    ring
  rw [hD, hM]
  simp only [map_sub, map_add, coeff_C_mul, coeff_mul_X_pow', coeff_mk]

open PowerSeries in
theorem OMA.aux_keyN (n : ℕ) :
    coeff n ((-2 * X * (256 * X ^ 2 + 320 * X + 1) : PowerSeries ℚ)) =
      -512 * (if n = 3 then 1 else 0) + -640 * (if n = 2 then 1 else 0)
        + -2 * (if n = 1 then 1 else 0) := by
  have hN : ((-2 * X * (256 * X ^ 2 + 320 * X + 1) : PowerSeries ℚ)) =
      C (-512) * X ^ 3 + C (-640) * X ^ 2 + C (-2) * X ^ 1 := by
    simp only [map_neg, map_ofNat]; ring
  rw [hN]
  simp only [map_add, coeff_C_mul, coeff_X_pow]

theorem OMA.aux_gf :
    PowerSeries.mk (fun n => if n = 0 then 0 else OMA.S_oeis_a167440.a n) =
      OMA.S_oeis_a167440.G := by
  unfold OMA.S_oeis_a167440.G
  rw [PowerSeries.eq_mul_inv_iff_mul_eq]
  · ext n
    rw [OMA.aux_keyD, OMA.aux_keyN]
    have ha1 : OMA.S_oeis_a167440.a 1 = 2 := by
      rw [OMA.aux_closed 1 (by omega)]; norm_num
    have ha2 : OMA.S_oeis_a167440.a 2 = 724 := by
      rw [OMA.aux_closed 2 (by omega)]; norm_num
    have ha3 : OMA.S_oeis_a167440.a 3 = 30248 := by
      rw [OMA.aux_closed 3 (by omega)]; norm_num
    obtain rfl | rfl | rfl | rfl | h4 :
        n = 0 ∨ n = 1 ∨ n = 2 ∨ n = 3 ∨ 4 ≤ n := by omega
    · norm_num
    · norm_num [ha1]
    · norm_num [ha1, ha2]
    · norm_num [ha1, ha2, ha3]
    · obtain ⟨k, rfl⟩ : ∃ k, n = k + 4 := ⟨n - 4, by omega⟩
      have e1 : k + 4 - 1 = k + 3 := by omega
      have e2 : k + 4 - 2 = k + 2 := by omega
      have e3 : k + 4 - 3 = k + 1 := by omega
      have i1 : 1 ≤ k + 4 := by omega
      have i2 : 2 ≤ k + 4 := by omega
      have i3 : 3 ≤ k + 4 := by omega
      have n1 : ¬ (k + 4 = 1) := by omega
      have n2 : ¬ (k + 4 = 2) := by omega
      have n3 : ¬ (k + 4 = 3) := by omega
      have z1 : ¬ (k + 1 = 0) := by omega
      have z2 : ¬ (k + 2 = 0) := by omega
      have z3 : ¬ (k + 3 = 0) := by omega
      have z4 : ¬ (k + 4 = 0) := by omega
      simp only [e1, e2, e3, if_pos i1, if_pos i2, if_pos i3, if_neg n1, if_neg n2, if_neg n3,
        if_neg z1, if_neg z2, if_neg z3, if_neg z4]
      have h := OMA.aux_rec (k + 4) (by omega)
      rw [e1, e2, e3] at h
      rw [h]
      ring
  · simp

theorem OMA.solution : type_of% @OMA.S_oeis_a167440.main :=
  ⟨OMA.aux_closed, OMA.aux_rec, OMA.aux_gf⟩
