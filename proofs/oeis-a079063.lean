import OMAStatements.S_oeis_a079063

-- SPDX-License-Identifier: Apache-2.0
-- Adapted from the-omega-institute/trureturing, commit
-- eef7e10c34c67d34647022c3e6e7a5473948dd95,
-- D5/S3/PrimeGaps/CloitreSquareRootPrimeGapRefutation.lean.
-- Changes: zero-based indices, fixed constant 2/5, checker entry point.

theorem OMA.h02_quadratic_step
    (c : ℝ) (N r m : ℕ) (hc : 0 < c)
    (hclaim : ∀ n : ℕ, N ≤ n → c * Real.sqrt n < (OMA.S_oeis_a079063.a n : ℝ))
    (hr : 1 < c * r) (hm : 1 ≤ m) (hN : N ≤ (r * m) ^ 2) :
    Real.sqrt (Nat.nth Nat.Prime ((r * (m + 1)) ^ 2)) ≤
      Real.sqrt (Nat.nth Nat.Prime ((r * m) ^ 2)) + (3 * r * r : ℕ) := by
  let t0 := (r * m) ^ 2
  let L := 3 * r * r
  have hlocal (t : ℕ) (ht : t0 ≤ t) :
      Real.sqrt (Nat.nth Nat.Prime (t + m)) ≤ Real.sqrt (Nat.nth Nat.Prime t) + 1 := by
    have hroot : (↑(r * m) : ℝ) ≤ Real.sqrt (↑t : ℝ) := by
      apply Real.le_sqrt_of_sq_le
      exact_mod_cast ht
    have hmreal : (0 : ℝ) < m := by exact_mod_cast hm
    have hmc : (m : ℝ) < c * (↑(r * m) : ℝ) := by
      have hmul := mul_lt_mul_of_pos_right hr hmreal
      simpa only [one_mul, Nat.cast_mul, mul_assoc] using hmul
    have hca : (m : ℝ) < (OMA.S_oeis_a079063.a t : ℝ) :=
      (hmc.trans_le (mul_le_mul_of_nonneg_left hroot hc.le)).trans
        (hclaim t (by omega))
    by_contra h
    have hdiff : 1 < Real.sqrt (Nat.nth Nat.Prime (t + m)) -
        Real.sqrt (Nat.nth Nat.Prime t) := by
      push Not at h
      linarith
    have hmem : m ∈ {j : ℕ |
        1 < Real.sqrt (Nat.nth Nat.Prime (t + j)) -
          Real.sqrt (Nat.nth Nat.Prime t)} := hdiff
    have hma : m < OMA.S_oeis_a079063.a t := by exact_mod_cast hca
    exact (not_lt_of_ge (Nat.sInf_le hmem)) hma
  have hchain (i : ℕ) :
      Real.sqrt (Nat.nth Nat.Prime (t0 + i * m)) ≤
        Real.sqrt (Nat.nth Nat.Prime t0) + i := by
    induction i with
    | zero => simp
    | succ i ih =>
      have hstep := hlocal (t0 + i * m) (Nat.le_add_right _ _)
      calc
        Real.sqrt (Nat.nth Nat.Prime (t0 + (i + 1) * m)) =
            Real.sqrt (Nat.nth Nat.Prime ((t0 + i * m) + m)) := by
              exact congrArg (fun j : ℕ => Real.sqrt (Nat.nth Nat.Prime j))
                (by simp only [Nat.add_mul, one_mul]; omega :
                  t0 + (i + 1) * m = (t0 + i * m) + m)
        _ ≤ Real.sqrt (Nat.nth Nat.Prime (t0 + i * m)) + 1 := hstep
        _ ≤ Real.sqrt (Nat.nth Nat.Prime t0) + (↑(i + 1) : ℝ) := by
          push_cast
          linarith [ih]
  have hR : r * r ≤ (r * r) * m := by
    calc
      r * r = (r * r) * 1 := by omega
      _ ≤ (r * r) * m := Nat.mul_le_mul_left _ hm
  have hindex : (r * (m + 1)) ^ 2 ≤ t0 + L * m := by
    dsimp [t0, L]
    nlinarith [hR]
  have hp := (Nat.nth_monotone Nat.infinite_setOfPred_prime) hindex
  have hs : Real.sqrt (Nat.nth Nat.Prime ((r * (m + 1)) ^ 2)) ≤
      Real.sqrt (Nat.nth Nat.Prime (t0 + L * m)) :=
    Real.sqrt_le_sqrt (by exact_mod_cast hp)
  exact hs.trans (by simpa only [t0, L] using hchain L)

theorem OMA.h02_quadratic_linear
    (c : ℝ) (N r : ℕ) (hc : 0 < c)
    (hclaim : ∀ n : ℕ, N ≤ n → c * Real.sqrt n < (OMA.S_oeis_a079063.a n : ℝ))
    (hr : 1 < c * r) :
    ∃ B : ℝ, 0 < B ∧ ∀ m : ℕ, N + 1 ≤ m →
      Real.sqrt (Nat.nth Nat.Prime ((r * m) ^ 2)) ≤ B * m := by
  have hr1 : 1 ≤ r := by
    by_contra h
    have hzero : r = 0 := by omega
    simp [hzero] at hr
    linarith
  let m0 := N + 1
  let L := 3 * r * r
  let B : ℝ := Real.sqrt (Nat.nth Nat.Prime ((r * m0) ^ 2)) + L
  have hL : (0 : ℝ) < L := by
    dsimp [L]
    have hrpos : 0 < r := by omega
    positivity
  have hB : 0 < B := by
    dsimp [B]
    exact add_pos_of_nonneg_of_pos (Real.sqrt_nonneg _) hL
  refine ⟨B, hB, ?_⟩
  intro m hm
  induction m, hm using Nat.le_induction with
  | base =>
    have hm0 : (1 : ℝ) ≤ m0 := by
      change (1 : ℝ) ≤ (N + 1 : ℕ)
      exact_mod_cast (by omega : 1 ≤ N + 1)
    have hB0 : 0 ≤ B := hB.le
    dsimp [B]
    nlinarith [mul_nonneg hB0 (sub_nonneg.mpr hm0)]
  | succ m hm ih =>
    have hN : N ≤ (r * m) ^ 2 := by
      have hNm : N ≤ m := by omega
      have hrm : m ≤ r * m := by
        calc
          m = 1 * m := by omega
          _ ≤ r * m := Nat.mul_le_mul_right m hr1
      have hx : 1 ≤ r * m := by omega
      have hpow : r * m ≤ (r * m) ^ 2 := by
        nlinarith [Nat.mul_le_mul_left (r * m) hx]
      exact hNm.trans (hrm.trans hpow)
    have hstep := OMA.h02_quadratic_step c N r m hc hclaim hr (by omega) hN
    have hLB : (L : ℝ) ≤ B := by
      dsimp [B]
      exact le_add_of_nonneg_left (Real.sqrt_nonneg _)
    calc
      Real.sqrt (Nat.nth Nat.Prime ((r * (m + 1)) ^ 2)) ≤
          Real.sqrt (Nat.nth Nat.Prime ((r * m) ^ 2)) + (L : ℝ) := by
            simpa only [L] using hstep
      _ ≤ B * (↑(m + 1) : ℝ) := by push_cast; nlinarith [ih, hLB]

theorem OMA.disproof : ¬ (type_of% @OMA.S_oeis_a079063.main) := by
  rintro ⟨N, hclaim⟩
  let c : ℝ := 2 / 5
  have hc : 0 < c := by norm_num [c]
  obtain ⟨r, hr0⟩ := exists_nat_gt (1 / c)
  have hr : 1 < c * (r : ℝ) := by
    have := (div_lt_iff₀ hc).mp hr0
    nlinarith
  obtain ⟨B, hB, hlinear⟩ := OMA.h02_quadratic_linear c N r hc hclaim hr
  let ε : ℝ := 1 / (2 * B ^ 2)
  have hε : 0 < ε := by dsimp [ε]; positivity
  have hev : ∀ᶠ x : ℝ in Filter.atTop,
      (Nat.primeCounting ⌊x⌋₊ : ℝ) ≤ ε * x := by
    filter_upwards [Chebyshev.eventually_primeCounting_le (show (0 : ℝ) < 1 by norm_num),
      Real.tendsto_log_atTop.eventually_ge_atTop ((Real.log 4 + 1) / ε),
      Filter.eventually_gt_atTop (1 : ℝ)] with x hpi hlog hx
    have hx0 : 0 ≤ x := le_trans (by norm_num : (0 : ℝ) ≤ 1) hx.le
    have hlogpos : 0 < Real.log x := Real.log_pos hx
    have hb : Real.log 4 + 1 ≤ ε * Real.log x := by
      have := (div_le_iff₀ hε).mp hlog
      nlinarith
    have hbound : (Real.log 4 + 1) * x / Real.log x ≤ ε * x := by
      apply (div_le_iff₀ hlogpos).2
      nlinarith [mul_le_mul_of_nonneg_right hb hx0]
    exact hpi.trans hbound
  obtain ⟨T, hT⟩ := Filter.eventually_atTop.1 hev
  obtain ⟨K, hK⟩ := exists_nat_gt T
  let m := N + K + 2
  have hm : N + 1 ≤ m := by dsimp [m]; omega
  have hmpos : 1 ≤ m := by omega
  have hr1 : 1 ≤ r := by
    by_contra h
    have hzero : r = 0 := by omega
    simp [hzero] at hr
    linarith
  have hindex : m ≤ (r * m) ^ 2 := by
    have hrm : m ≤ r * m := by
      calc
        m = 1 * m := by omega
        _ ≤ r * m := Nat.mul_le_mul_right m hr1
    have hx : 1 ≤ r * m := by omega
    have hpow : r * m ≤ (r * m) ^ 2 := by
      nlinarith [Nat.mul_le_mul_left (r * m) hx]
    exact hrm.trans hpow
  let q := Nat.nth Nat.Prime ((r * m) ^ 2)
  have hmq : m ≤ q :=
    hindex.trans ((Nat.le_add_right _ _).trans (Nat.add_two_le_nth_prime _))
  have hTq : T ≤ (q : ℝ) := by
    have hKm : K ≤ m := by dsimp [m]; omega
    have hKq : (K : ℝ) ≤ q := by exact_mod_cast hKm.trans hmq
    exact hK.le.trans hKq
  have hsmall : (Nat.primeCounting q : ℝ) ≤ ε * q := by
    simpa only [Nat.floor_natCast] using hT (q : ℝ) hTq
  have hcount : ((r * m) ^ 2 : ℕ) ≤ Nat.primeCounting q := by
    have hmono := Nat.monotone_primeCounting' (Nat.le_succ q)
    simpa only [q, Nat.primeCounting, Nat.primeCounting'_nth_eq] using hmono
  have hlin : Real.sqrt (q : ℝ) ≤ B * m := hlinear m hm
  have hq : (q : ℝ) ≤ B ^ 2 * (m : ℝ) ^ 2 := by
    have hsq : (Real.sqrt (q : ℝ)) ^ 2 = q := Real.sq_sqrt (by positivity)
    nlinarith [mul_nonneg (sub_nonneg.mpr hlin)
      (add_nonneg (Real.sqrt_nonneg (q : ℝ)) (by positivity : 0 ≤ B * (m : ℝ)))]
  have hcountRCast : (((r * m) ^ 2 : ℕ) : ℝ) ≤ (Nat.primeCounting q : ℝ) := by
    exact_mod_cast hcount
  have hcountR : (((r * m) ^ 2 : ℕ) : ℝ) ≤ ε * q :=
    hcountRCast.trans hsmall
  have hmR : (0 : ℝ) < m := by exact_mod_cast hmpos
  have hrR : (1 : ℝ) ≤ r := by exact_mod_cast hr1
  have hεB : ε * B ^ 2 = 1 / 2 := by
    dsimp [ε]
    field_simp
  have hsmallR : (((r * m) ^ 2 : ℕ) : ℝ) ≤ (m : ℝ) ^ 2 / 2 := by
    calc
      (((r * m) ^ 2 : ℕ) : ℝ) ≤ ε * (q : ℝ) := hcountR
      _ ≤ ε * (B ^ 2 * (m : ℝ) ^ 2) := mul_le_mul_of_nonneg_left hq hε.le
      _ = (m : ℝ) ^ 2 / 2 := by rw [← mul_assoc, hεB]; ring
  have hr2 : (1 : ℝ) ≤ (r : ℝ) ^ 2 := by nlinarith [sq_nonneg ((r : ℝ) - 1)]
  have hm2 : 0 < (m : ℝ) ^ 2 := sq_pos_of_pos hmR
  have hbound : (m : ℝ) ^ 2 ≤ ((r : ℝ) * m) ^ 2 := by
    nlinarith [mul_nonneg (sub_nonneg.mpr hr2) hm2.le]
  push_cast at hsmallR
  nlinarith [hbound, hm2]
