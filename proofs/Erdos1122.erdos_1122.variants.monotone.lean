import FormalConjectures.ErdosProblems.«1122»

open Filter Topology

set_option maxHeartbeats 1000000 in
theorem OMA.solution : type_of% @Erdos1122.erdos_1122.variants.monotone := by
  intro f hf hmono
  have hf1 : f 1 = 0 := by have := hf 1 (by decide) 1 (by decide) (by decide); linarith
  have hle {a b : ℕ} (ha : 1 ≤ a) (hab : a ≤ b) : f a ≤ f b :=
    Nat.le_induction le_rfl (fun _ hb ih => ih.trans (hmono _ (ha.trans hb))) b hab
  have hgr (i : ℕ) : f (2 ^ (i + 1) + 1) ≤ i * f 2 + f 3 := by
    induction i with
    | zero => norm_num
    | succ i ih =>
      have hc : (2 : ℕ).Coprime (2 ^ (i + 1) + 1) := by
        rw [pow_succ', Nat.coprime_mul_left_add_right]; simp
      have := hle (Nat.succ_le_iff.2 (by positivity))
        (show 2 ^ (i + 1 + 1) + 1 ≤ 2 * (2 ^ (i + 1) + 1) by rw [pow_succ']; omega)
      rw [hf 2 (by decide) _ (by positivity) hc] at this; push_cast; linarith
  have hsg (m : ℕ) (e : ℝ) (he : 0 < e) :
      ∃ a, 0 < a ∧ m.Coprime a ∧ f (a + 2 * m) - f a < e := by
    let K := 2 * m; let q (j : ℕ) := 1 + K * j
    by_contra h
    have hgap (j : ℕ) : e ≤ f (q (j + 1)) - f (q j) := by
      by_contra! hlt; apply h
      refine ⟨q j, by dsimp [q]; omega, ?_, by rwa [show q j + 2 * m = q (j + 1) by dsimp [q, K]; ring]⟩
      change Nat.Coprime m (1 + 2 * m * j)
      rw [show 2 * m * j = 2 * j * m by ring, Nat.coprime_add_mul_right_right]; simp
    have hlin (j : ℕ) : (j : ℝ) * e ≤ f (q j) := by
      induction j with
      | zero => simp [q, hf1]
      | succ j ih => have := hgap j; push_cast; linarith
    have hb (i : ℕ) : e ≤ (((i : ℝ) + K) * f 2 + f 3) / (2 : ℝ) ^ i := by
      refine (le_div_iff₀ (by positivity)).2 ?_
      have hK : K ≤ 2 ^ (K + 1) :=
        K.lt_two_pow_self.le.trans (Nat.pow_le_pow_right (by decide) (by omega))
      have hcmp : q (2 ^ i) ≤ 2 ^ (i + K + 1) + 1 := by
        calc 1 + K * 2 ^ i ≤ 1 + 2 ^ (K + 1) * 2 ^ i := Nat.add_le_add_left (Nat.mul_le_mul_right _ hK) _
          _ = 2 ^ (i + K + 1) + 1 := by rw [← pow_add, show K + 1 + i = i + K + 1 by omega, Nat.add_comm]
      have h1 := hlin (2 ^ i); have h2 := hle (by dsimp [q]; omega) hcmp; have h3 := hgr (i + K)
      push_cast at h1 h3; linarith
    have hlim : Tendsto (fun i : ℕ => (((i : ℝ) + K) * f 2 + f 3) / (2 : ℝ) ^ i) atTop (𝓝 0) := by
      have h1 := tendsto_pow_const_div_const_pow_of_one_lt 1 (show (1 : ℝ) < 2 by norm_num)
      have h0 := tendsto_pow_const_div_const_pow_of_one_lt 0 (show (1 : ℝ) < 2 by norm_num)
      simp only [pow_one, pow_zero] at h1 h0
      have hs := (h1.const_mul (f 2)).add (h0.const_mul ((K : ℝ) * f 2 + f 3))
      rw [mul_zero, mul_zero, add_zero] at hs
      exact hs.congr fun i => by ring
    exact not_le_of_gt he (le_of_tendsto_of_tendsto' tendsto_const_nhds hlim hb)
  have hps (m : ℕ) (hm : 0 < m) (r : ℕ) : f (m ^ (r + 1)) = f (m ^ r) + f m := by
    by_cases hm1 : m = 1
    · simp [hm1, hf1]
    have hbd (e : ℝ) (he : 0 < e) : |f (m ^ (r + 1)) - (f (m ^ r) + f m)| ≤ e := by
      obtain ⟨a, ha, hcop, hgap⟩ := hsg m e he
      let x := a + m
      have hx : 0 < x := by dsimp [x]; omega
      have hmx : 1 < m * x := (show 1 < m by omega).trans_le (Nat.le_mul_of_pos_right _ hx)
      have hplus : m.Coprime (m * x + 1) := by rw [Nat.coprime_mul_left_add_right]; simp
      have hmin : m.Coprime (m * x - 1) :=
        Nat.Coprime.of_dvd_left (dvd_mul_right m x)
          ((Nat.coprime_self_sub_right (by omega)).2 (by simp))
      have hmid : f (m ^ (r + 1) * x) = f (m ^ (r + 1)) + f x :=
        hf _ (by positivity) _ hx ((Nat.coprime_add_self_right.2 hcop).pow_left _)
      have hax : f a ≤ f x := hle ha (by dsimp [x]; omega)
      have hxb : f x ≤ f (a + 2 * m) := hle hx (by dsimp [x]; omega)
      have hmsq : 0 < m * m := Nat.mul_pos hm hm
      have hlo : f (m ^ r) + f m + f a ≤ f (m ^ (r + 1)) + f x := by
        have h1 : f (m * a) ≤ f (m * x - 1) :=
          hle (Nat.mul_pos hm ha) (by rw [show m * x = m * a + m * m by dsimp [x]; ring]; omega)
        have h2 : f (m ^ r * (m * x - 1)) ≤ f (m ^ (r + 1) * x) :=
          hle (Nat.mul_pos (pow_pos hm r) (by omega))
            (by rw [pow_succ, Nat.mul_assoc]; exact Nat.mul_le_mul_left _ (Nat.sub_le _ _))
        rw [hf m hm a ha hcop] at h1
        rw [hf _ (by positivity) _ (by omega) (hmin.pow_left _), hmid] at h2
        linarith
      have hup : f (m ^ (r + 1)) + f x ≤ f (m ^ r) + f m + f (a + 2 * m) := by
        have h1 : f (m ^ (r + 1) * x) ≤ f (m ^ r * (m * x + 1)) :=
          hle (Nat.mul_pos (pow_pos hm _) hx)
            (by rw [pow_succ, Nat.mul_assoc]; exact Nat.mul_le_mul_left _ (Nat.le_succ _))
        have h2 : f (m * x + 1) ≤ f (m * (a + 2 * m)) :=
          hle (by omega) (by rw [show m * (a + 2 * m) = m * x + m * m by dsimp [x]; ring]; omega)
        rw [hmid, hf _ (by positivity) _ (by positivity) (hplus.pow_left _)] at h1
        rw [hf m hm _ (by omega) ((Nat.coprime_add_mul_right_right m a 2).2 hcop)] at h2
        linarith
      exact abs_le.2 ⟨by linarith, by linarith⟩
    by_contra hne
    have hp := abs_pos.2 (sub_ne_zero.2 hne); have := hbd _ (half_pos hp); linarith
  have hpow (a : ℕ) (ha : 0 < a) (r : ℕ) : f (a ^ r) = r * f a := by
    induction r with
    | zero => simp [hf1]
    | succ r ih => rw [hps a ha r, ih]; push_cast; ring
  have hl2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hf2 : 0 ≤ f 2 := hf1 ▸ hle (by decide) (by decide)
  let c := f 2 / Real.log 2
  have hc : 0 ≤ c := div_nonneg hf2 hl2.le
  have hcl : c * Real.log 2 = f 2 := div_mul_cancel₀ _ hl2.ne'
  refine ⟨c, fun n hn => ?_⟩
  have hbd (t : ℕ) : |(t : ℝ) * (f n - c * Real.log n)| ≤ f 2 := by
    let k := Nat.log 2 (n ^ t)
    have hlo : 2 ^ k ≤ n ^ t := Nat.pow_log_le_self _ (pow_ne_zero _ hn.ne')
    have hhi : n ^ t ≤ 2 ^ (k + 1) := (Nat.lt_pow_succ_log_self (by decide) _).le
    have hfl := hle (pow_pos (by decide : 0 < 2) k) hlo
    have hfh := hle (pow_pos hn t) hhi
    rw [hpow 2 (by decide), hpow n hn] at hfl hfh
    have hll : (k : ℝ) * Real.log 2 ≤ t * Real.log n := by
      simpa only [Nat.cast_pow, Nat.cast_ofNat, Real.log_pow] using
        Real.log_le_log (show (0 : ℝ) < ((2 ^ k : ℕ) : ℝ) by positivity)
          (show ((2 ^ k : ℕ) : ℝ) ≤ ((n ^ t : ℕ) : ℝ) by exact_mod_cast hlo)
    have hlh : (t : ℝ) * Real.log n ≤ ((k + 1 : ℕ) : ℝ) * Real.log 2 := by
      simpa only [Nat.cast_pow, Nat.cast_ofNat, Real.log_pow] using
        Real.log_le_log (show (0 : ℝ) < ((n ^ t : ℕ) : ℝ) by positivity)
          (show ((n ^ t : ℕ) : ℝ) ≤ ((2 ^ (k + 1) : ℕ) : ℝ) by exact_mod_cast hhi)
    have hcl1 : (k : ℝ) * f 2 ≤ t * (c * Real.log n) := by
      rw [← hcl]; simpa only [mul_left_comm] using mul_le_mul_of_nonneg_left hll hc
    have hch1 : (t : ℝ) * (c * Real.log n) ≤ ((k + 1 : ℕ) : ℝ) * f 2 := by
      rw [← hcl]; simpa only [mul_left_comm] using mul_le_mul_of_nonneg_left hlh hc
    push_cast at hfh hch1; rw [mul_sub]; exact abs_le.2 ⟨by nlinarith, by nlinarith⟩
  by_contra hne
  have hpos := abs_pos.2 (sub_ne_zero.2 hne)
  obtain ⟨t, ht⟩ := exists_nat_gt (f 2 / |f n - c * Real.log n|)
  have hsm := hbd t; rw [abs_mul, abs_of_nonneg (Nat.cast_nonneg t)] at hsm
  exact not_lt_of_ge hsm ((div_lt_iff₀ hpos).1 ht)
