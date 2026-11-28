import OMAStatements.S_oeis_a076821

open scoped Nat.Prime

private lemma helper_sum_cube_le {N : ℕ} (hN : 0 < N) {pN S : ℝ}
    (hpN_nonneg : 0 ≤ pN) (hS_pos : 0 < S)
    {d : ℕ → ℝ} (hd_pos : ∀ n, 0 < d n)
    (hsum_d_le : ∑ n ∈ Finset.range N, d n ≤ pN)
    (hsum_f : ∑ n ∈ Finset.range N, (1 / d n) ^ 2 ≤ S) :
    (N : ℝ) ^ 3 ≤ pN ^ 2 * S := by
  have hN_pos : (0 : ℝ) < (N : ℝ) := Nat.cast_pos.mpr hN
  have hsum_d_pos : 0 < ∑ n ∈ Finset.range N, d n :=
    Finset.sum_pos (fun n _ => hd_pos n) ⟨0, Finset.mem_range.mpr hN⟩
  have hsed1 :
      (N : ℝ) ^ 2 / ∑ n ∈ Finset.range N, d n ≤ ∑ n ∈ Finset.range N, 1 / d n := by
    have h := Finset.sq_sum_div_le_sum_sq_div (Finset.range N) (fun _ => (1 : ℝ))
      (fun n _ => hd_pos n)
    simpa only [Finset.sum_const, Finset.card_range, nsmul_eq_mul, mul_one, one_pow] using h
  have hsed2 :
      (∑ n ∈ Finset.range N, 1 / d n) ^ 2 / (N : ℝ) ≤ ∑ n ∈ Finset.range N, (1 / d n) ^ 2 := by
    have h := Finset.sq_sum_div_le_sum_sq_div (Finset.range N) (fun n => 1 / d n)
      (fun _ _ => zero_lt_one)
    simpa only [Finset.sum_const, Finset.card_range, nsmul_eq_mul, mul_one, div_one] using h
  have h1 : ((N : ℝ) ^ 2 / ∑ n ∈ Finset.range N, d n) ^ 2 ≤ (N : ℝ) * S := by
    have ha := pow_le_pow_left₀ (div_nonneg (sq_nonneg _) hsum_d_pos.le) hsed1 2
    have hb : (∑ n ∈ Finset.range N, 1 / d n) ^ 2 ≤ (N : ℝ) * S :=
      (div_le_iff₀ hN_pos).mp (hsed2.trans hsum_f) |>.trans_eq (mul_comm _ _)
    exact ha.trans hb
  have hsum_d_sq_le : (∑ n ∈ Finset.range N, d n) ^ 2 ≤ pN ^ 2 :=
    pow_le_pow_left₀ hsum_d_pos.le hsum_d_le 2
  have hsum_d_sq_pos : 0 < (∑ n ∈ Finset.range N, d n) ^ 2 := sq_pos_of_pos hsum_d_pos
  rw [div_pow, div_le_iff₀ hsum_d_sq_pos] at h1
  have h4 : (N : ℝ) ^ 4 ≤ (N : ℝ) * (pN ^ 2 * S) := by
    calc (N : ℝ) ^ 4 = ((N : ℝ) ^ 2) ^ 2 := by ring
      _ ≤ (N : ℝ) * S * (∑ n ∈ Finset.range N, d n) ^ 2 := h1
      _ ≤ (N : ℝ) * S * pN ^ 2 := by gcongr
      _ = (N : ℝ) * (pN ^ 2 * S) := by ring
  rw [show (N : ℝ) ^ 4 = (N : ℝ) * (N : ℝ) ^ 3 by ring] at h4
  exact le_of_mul_le_mul_left h4 hN_pos

private lemma helper_chebyshev_bound {N pN : ℕ} (hN_ge : 10001 ≤ N)
    (hpN_ge : N + 2 ≤ pN) (hpi : Nat.primeCounting (pN - 1) = N) :
    (pN : ℝ) ^ 6 ≤ (16 : ℝ) ^ 8 * (N : ℝ) ^ 8 := by
  have hpN_10003 : 10003 ≤ pN := by omega
  have hN_pos : (0 : ℝ) < (N : ℝ) := by exact_mod_cast (by omega : 0 < N)
  have hpN_pos : (0 : ℝ) < (pN : ℝ) := by exact_mod_cast (by omega : 0 < pN)
  let m : ℕ := pN - 1
  have hm_ge : 10002 ≤ m := by omega
  have hm_succ : m + 1 = pN := by omega
  have hm_gt_one : (1 : ℝ) < (m : ℝ) := by exact_mod_cast (by omega : 1 < m)
  have hm_pos : (0 : ℝ) < (m : ℝ) := lt_trans zero_lt_one hm_gt_one
  have hcheb := Chebyshev.pi_ge m
  change ((m : ℝ) * Real.log 2 - Real.log ((m : ℝ) + 1)) / Real.log (m : ℝ) ≤
    (Nat.primeCounting m : ℝ) at hcheb
  rw [hpi] at hcheb
  have hcheb' : (m : ℝ) * Real.log 2 - Real.log ((m : ℝ) + 1) ≤ (N : ℝ) * Real.log (m : ℝ) :=
    (div_le_iff₀ (Real.log_pos hm_gt_one)).mp hcheb
  have hm1_eq : (m : ℝ) + 1 = (pN : ℝ) := by exact_mod_cast hm_succ
  have hm_cast : (m : ℝ) = (pN : ℝ) - 1 := by linarith only [hm1_eq]
  rw [hm1_eq] at hcheb'
  let u : ℝ := Real.sqrt (Real.sqrt (pN : ℝ))
  have hu_sq : u ^ 2 = Real.sqrt (pN : ℝ) := Real.sq_sqrt (Real.sqrt_nonneg _)
  have hu_pow4 : u ^ 4 = (pN : ℝ) := by
    calc u ^ 4 = (u ^ 2) ^ 2 := by ring
      _ = (Real.sqrt (pN : ℝ)) ^ 2 := by rw [hu_sq]
      _ = (pN : ℝ) := Real.sq_sqrt hpN_pos.le
  have hu_ge10 : 10 ≤ u := by
    have hpN_real : (10 : ℝ) ^ 4 ≤ (pN : ℝ) := by exact_mod_cast (by omega : 10 ^ 4 ≤ pN)
    have hsqrt1 : (100 : ℝ) ≤ Real.sqrt (pN : ℝ) := by
      rw [show (100 : ℝ) = Real.sqrt (10 ^ 4) by norm_num]
      exact Real.sqrt_le_sqrt hpN_real
    rw [show (10 : ℝ) = Real.sqrt 100 by norm_num]
    exact Real.sqrt_le_sqrt hsqrt1
  have hu_pos : 0 < u := by linarith only [hu_ge10]
  have hlog_pN : Real.log (pN : ℝ) ≤ 4 * u := by
    rw [← hu_pow4, Real.log_pow]
    have hlu : Real.log u ≤ u - 1 := Real.log_le_sub_one_of_pos hu_pos
    norm_num
    linarith only [hlu]
  have hlog_m_le : Real.log (m : ℝ) ≤ 4 * u := by
    have hm_le_pN : (m : ℝ) ≤ (pN : ℝ) := by exact_mod_cast (by omega : m ≤ pN)
    exact (Real.log_le_log hm_pos hm_le_pN).trans hlog_pN
  have hlog2 : (1 / 2 : ℝ) < Real.log 2 := by linarith only [Real.log_two_gt_d9]
  have hm_nonneg : 0 ≤ (m : ℝ) := hm_pos.le
  have hleft : (1 / 2 : ℝ) * (m : ℝ) - 4 * u ≤ (m : ℝ) * Real.log 2 - Real.log (pN : ℝ) := by
    have hmul : (m : ℝ) * (1 / 2) ≤ (m : ℝ) * Real.log 2 :=
      mul_le_mul_of_nonneg_left hlog2.le hm_nonneg
    linarith only [hmul, hlog_pN]
  have hright : (N : ℝ) * Real.log (m : ℝ) ≤ (N : ℝ) * (4 * u) :=
    mul_le_mul_of_nonneg_left hlog_m_le hN_pos.le
  have hineq : (1 / 2 : ℝ) * (u ^ 4 - 1) - 4 * u ≤ 4 * (N : ℝ) * u := by
    have hcomb := (hleft.trans hcheb').trans hright
    linarith only [hcomb, hm_cast, hu_pow4]
  have hu3_ge : 1000 ≤ u ^ 3 := by
    have h1 := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ 10) hu_ge10 3
    norm_num at h1
    exact h1
  have hu_poly : (1 / 4 : ℝ) * u ^ 4 ≤ (1 / 2 : ℝ) * (u ^ 4 - 1) - 4 * u := by
    have hmul : 20 * u ≤ u ^ 4 := by
      have h20 : (20 : ℝ) ≤ u ^ 3 := by linarith only [hu3_ge]
      calc 20 * u ≤ u ^ 3 * u := mul_le_mul_of_nonneg_right h20 hu_pos.le
        _ = u ^ 4 := by ring
    linarith only [hmul, hu_ge10]
  have hu4_le : (1 / 4 : ℝ) * u ^ 4 ≤ 4 * (N : ℝ) * u := hu_poly.trans hineq
  have hu3_le : u ^ 3 ≤ 16 * (N : ℝ) := by
    have h4 : u * u ^ 3 ≤ u * (16 * (N : ℝ)) := by linarith only [hu4_le]
    exact le_of_mul_le_mul_left h4 hu_pos
  have hpow := pow_le_pow_left₀ (pow_nonneg hu_pos.le 3) hu3_le 8
  calc (pN : ℝ) ^ 6 = (u ^ 4) ^ 6 := by rw [hu_pow4]
    _ = (u ^ 3) ^ 8 := by ring
    _ ≤ (16 * (N : ℝ)) ^ 8 := hpow
    _ = (16 : ℝ) ^ 8 * (N : ℝ) ^ 8 := by ring

theorem OMA.solution : type_of% @OMA.S_oeis_a076821.main := by
  intro hsum
  let p : ℕ → ℕ := Nat.nth Nat.Prime
  let f : ℕ → ℝ := fun n =>
    (1 : ℝ) / (((p (n + 1) - p n : ℕ) : ℝ) ^ 2)
  let S : ℝ := max (∑' n, f n) 1
  have hS_pos : 0 < S := lt_of_lt_of_le zero_lt_one (le_max_right _ _)
  have hf_le_S : ∀ N : ℕ, ∑ n ∈ Finset.range N, f n ≤ S := fun N =>
    (hsum.sum_le_tsum (Finset.range N) (fun _ _ => by positivity)).trans (le_max_left _ _)
  let N : ℕ := Nat.ceil ((16 : ℝ) ^ 8 * S ^ 3) + 10001
  have hN_ge : 10001 ≤ N := Nat.le_add_left _ _
  have hN_pos : (0 : ℝ) < (N : ℝ) := by exact_mod_cast (by omega : 0 < N)
  have hN_gt : (16 : ℝ) ^ 8 * S ^ 3 < (N : ℝ) := by
    have h1 : (16 : ℝ) ^ 8 * S ^ 3 ≤ Nat.ceil ((16 : ℝ) ^ 8 * S ^ 3) := Nat.le_ceil _
    have h2 : (Nat.ceil ((16 : ℝ) ^ 8 * S ^ 3) : ℝ) < (N : ℝ) := by
      exact_mod_cast (by omega : Nat.ceil ((16 : ℝ) ^ 8 * S ^ 3) < N)
    linarith only [h1, h2]
  have hp_lt : ∀ n, p n < p (n + 1) := fun n =>
    Nat.nth_strictMono Nat.infinite_setOfPred_prime (Nat.lt_succ_self n)
  let d : ℕ → ℝ := fun n => (p (n + 1) : ℝ) - (p n : ℝ)
  have hd_eq : ∀ n, ((p (n + 1) - p n : ℕ) : ℝ) = d n := fun n => by
    rw [Nat.cast_sub (hp_lt n).le]
  have hd_pos : ∀ n, 0 < d n := fun n =>
    sub_pos.mpr (Nat.cast_lt.mpr (hp_lt n))
  have hsum_f : ∑ n ∈ Finset.range N, (1 / d n) ^ 2 ≤ S := by
    have hcongr : ∑ n ∈ Finset.range N, (1 / d n) ^ 2 = ∑ n ∈ Finset.range N, f n := by
      refine Finset.sum_congr rfl fun n _ => ?_
      simp only [f, hd_eq n, one_div, inv_pow]
    rw [hcongr]
    exact hf_le_S N
  have hsum_d_le : ∑ n ∈ Finset.range N, d n ≤ (p N : ℝ) := by
    rw [Finset.sum_range_sub (fun n => (p n : ℝ)) N]
    have h0 : (0 : ℝ) ≤ (p 0 : ℝ) := Nat.cast_nonneg _
    linarith only [h0]
  have hN3 : (N : ℝ) ^ 3 ≤ (p N : ℝ) ^ 2 * S :=
    helper_sum_cube_le (by omega) (Nat.cast_nonneg _) hS_pos hd_pos hsum_d_le hsum_f
  have hpi : Nat.primeCounting (p N - 1) = N := by
    change Nat.primeCounting (Nat.nth Nat.Prime N - 1) = N
    rw [Nat.primeCounting_sub_one, Nat.primeCounting'_nth_eq]
  have hpN6 : (p N : ℝ) ^ 6 ≤ (16 : ℝ) ^ 8 * (N : ℝ) ^ 8 :=
    helper_chebyshev_bound hN_ge (Nat.add_two_le_nth_prime N) hpi
  have hN9 : (N : ℝ) ^ 9 ≤ (16 : ℝ) ^ 8 * (N : ℝ) ^ 8 * S ^ 3 := by
    have hcub := pow_le_pow_left₀ (by positivity) hN3 3
    calc (N : ℝ) ^ 9 = ((N : ℝ) ^ 3) ^ 3 := by ring
      _ ≤ ((p N : ℝ) ^ 2 * S) ^ 3 := hcub
      _ = (p N : ℝ) ^ 6 * S ^ 3 := by ring
      _ ≤ ((16 : ℝ) ^ 8 * (N : ℝ) ^ 8) * S ^ 3 := by gcongr
      _ = (16 : ℝ) ^ 8 * (N : ℝ) ^ 8 * S ^ 3 := by ring
  have hN8_pos : 0 < (N : ℝ) ^ 8 := pow_pos hN_pos 8
  have hN_le : (N : ℝ) ≤ (16 : ℝ) ^ 8 * S ^ 3 := by
    have hmul : (N : ℝ) ^ 8 * (N : ℝ) ≤ (N : ℝ) ^ 8 * ((16 : ℝ) ^ 8 * S ^ 3) := by
      linarith only [hN9, show (N : ℝ) ^ 8 * (N : ℝ) = (N : ℝ) ^ 9 by ring,
        show (N : ℝ) ^ 8 * ((16 : ℝ) ^ 8 * S ^ 3) = (16 : ℝ) ^ 8 * (N : ℝ) ^ 8 * S ^ 3 by ring]
    exact le_of_mul_le_mul_left hmul hN8_pos
  linarith only [hN_le, hN_gt]
