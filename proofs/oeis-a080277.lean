import OMAStatements.S_oeis_a080277

-- Problem: A080277: Partial sums of A038712.
-- Upstream: formal-conjectures statements/oeis-a080277.lean:0 (declaration OMA.S_oeis_a080277.main)
-- Credit: @agchua (the owner of the agent is credited as the solver)
-- Prove EXACTLY this target. No sorry, no axiom, no native_decide.
-- Idea: A038712(2k+1) = 1 and A038712(2k) = 2 A038712(k) + 1, so a(2m) = 2a(m) + 2m and
-- a(n) = n + 2a(n/2). With L = Nat.log 2 n, strong induction gives L + 1 - n <= a(n) - nL <= n.
-- Since L <= log n / log 2 < L + 1, the ratio a(n) / (n log n / log 2) lies between
-- 1 - 2/l and 1 + 1/l with l = log n / log 2, which tends to infinity (squeeze).

namespace H13A080277

open OMA.S_oeis_a080277

theorem f_odd (k : ℕ) : A038712 (2 * k + 1) = 1 := by
  have h0 : padicValNat 2 (2 * k + 1) = 0 := padicValNat.eq_zero_of_not_dvd (by omega)
  simp [A038712, h0]

theorem f_even (k : ℕ) (hk : 1 ≤ k) : A038712 (2 * k) = 2 * A038712 k + 1 := by
  have hm : padicValNat 2 (2 * k) = padicValNat 2 2 + padicValNat 2 k :=
    padicValNat.mul (by norm_num) (by omega)
  have h2 : padicValNat 2 2 = 1 := padicValNat.self (by norm_num)
  have hp : 2 ^ (padicValNat 2 k + 1 + 1) = 2 * 2 ^ (padicValNat 2 k + 1) := by ring
  have h1 : 1 ≤ 2 ^ (padicValNat 2 k + 1) := Nat.one_le_two_pow
  unfold A038712
  rw [hm, h2, show 1 + padicValNat 2 k + 1 = padicValNat 2 k + 1 + 1 by omega, hp]
  omega

theorem a_succ (n : ℕ) : a (n + 1) = a n + A038712 (n + 1) := by
  unfold a
  rw [Finset.sum_Icc_succ_top (by omega)]

theorem a_two (m : ℕ) : a (2 * m) = 2 * a m + 2 * m := by
  induction m with
  | zero => simp [a]
  | succ m ih =>
    have s1 := a_succ (2 * m + 1)
    have s2 := a_succ (2 * m)
    have s3 := a_succ m
    have o1 := f_odd m
    have e2 := f_even (m + 1) (by omega)
    rw [show 2 * (m + 1) = 2 * m + 1 + 1 by ring] at e2
    rw [show 2 * (m + 1) = 2 * m + 1 + 1 by ring]
    omega

theorem a_rec (n : ℕ) : a n = n + 2 * a (n / 2) := by
  obtain ⟨m, rfl | rfl⟩ := Nat.even_or_odd' n
  · rw [show 2 * m / 2 = m by omega, a_two]
    omega
  · rw [show (2 * m + 1) / 2 = m by omega, a_succ, a_two, f_odd]
    omega

theorem bounds : ∀ n : ℕ, 1 ≤ n →
    ((Nat.log 2 n : ℝ) + 1 - n ≤ (a n : ℝ) - n * Nat.log 2 n) ∧
    ((a n : ℝ) - n * Nat.log 2 n ≤ n) := by
  intro n
  refine Nat.strong_induction_on n ?_
  intro n ih hn
  rcases Nat.lt_or_ge n 2 with h | h
  · obtain rfl : n = 1 := by omega
    have ha1 : a 1 = 1 := by
      rw [a_rec 1]
      simp [a]
    norm_num [ha1]
  · obtain ⟨m, hm⟩ : ∃ m, n / 2 = m := ⟨_, rfl⟩
    obtain ⟨e, he⟩ : ∃ e, n % 2 = e := ⟨_, rfl⟩
    obtain ⟨ihl, ihu⟩ := ih m (by omega) (by omega)
    have hL : Nat.log 2 n = Nat.log 2 m + 1 := by
      rw [← hm]
      exact Nat.log_of_one_lt_of_le (by norm_num) h
    have hr : a n = n + 2 * a m := by
      rw [← hm]
      exact a_rec n
    have hd : n = 2 * m + e := by omega
    have h1 : (a n : ℝ) = n + 2 * a m := by exact_mod_cast hr
    have h2 : (n : ℝ) = 2 * m + e := by exact_mod_cast hd
    have h3 : (Nat.log 2 n : ℝ) = Nat.log 2 m + 1 := by exact_mod_cast hL
    have hg : (a n : ℝ) - n * Nat.log 2 n =
        2 * ((a m : ℝ) - m * Nat.log 2 m) - e * Nat.log 2 m := by
      linear_combination h1 - (n : ℝ) * h3 - (Nat.log 2 m : ℝ) * h2
    have hL0 : (0 : ℝ) ≤ Nat.log 2 m := Nat.cast_nonneg _
    rcases (show e = 0 ∨ e = 1 by omega) with h0 | h0
    · have h0' : (e : ℝ) = 0 := by exact_mod_cast h0
      rw [h0'] at hg h2
      constructor
      · linarith
      · linarith
    · have h0' : (e : ℝ) = 1 := by exact_mod_cast h0
      rw [h0'] at hg h2
      constructor
      · linarith
      · linarith

theorem pointwise (n : ℕ) (hn : 2 ≤ n) :
    1 - 2 * (Real.log n / Real.log 2)⁻¹ ≤ (a n : ℝ) / (n * Real.log n / Real.log 2) ∧
    (a n : ℝ) / (n * Real.log n / Real.log 2) ≤ 1 + (Real.log n / Real.log 2)⁻¹ := by
  obtain ⟨hl, hu⟩ := bounds n (by omega)
  have hlog2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hpowle : 2 ^ Nat.log 2 n ≤ n := Nat.pow_log_le_self 2 (by omega)
  have hltpow : n < 2 ^ (Nat.log 2 n + 1) := Nat.lt_pow_succ_log_self (by norm_num) n
  have hL1 : 0 < Nat.log 2 n := Nat.log_pos (by norm_num) hn
  have hnR : (0 : ℝ) < n := by exact_mod_cast (show 0 < n by omega)
  have hA : (Nat.log 2 n : ℝ) * Real.log 2 ≤ Real.log n := by
    have hx : (2 : ℝ) ^ Nat.log 2 n ≤ n := by exact_mod_cast hpowle
    have h := Real.log_le_log (by positivity) hx
    rw [Real.log_pow] at h
    exact h
  have hB : Real.log n < ((Nat.log 2 n : ℝ) + 1) * Real.log 2 := by
    have hx : (n : ℝ) < (2 : ℝ) ^ (Nat.log 2 n + 1) := by exact_mod_cast hltpow
    have h := Real.log_lt_log hnR hx
    rw [Real.log_pow] at h
    push_cast at h
    exact h
  obtain ⟨l, hl'⟩ : ∃ l : ℝ, l = Real.log n / Real.log 2 := ⟨_, rfl⟩
  have hlL : (Nat.log 2 n : ℝ) ≤ l := by
    rw [hl']
    exact (le_div_iff₀ hlog2).mpr hA
  have hlU : l < (Nat.log 2 n : ℝ) + 1 := by
    rw [hl']
    exact (div_lt_iff₀ hlog2).mpr hB
  have hL1' : 1 ≤ Nat.log 2 n := hL1
  have hL1R : (1 : ℝ) ≤ Nat.log 2 n := by exact_mod_cast hL1'
  have hlpos : 0 < l := by linarith
  have hk : (n : ℝ) * (l⁻¹ * l) = n := by
    rw [inv_mul_cancel₀ (ne_of_gt hlpos), mul_one]
  have hnl : (n : ℝ) * Nat.log 2 n ≤ n * l := mul_le_mul_of_nonneg_left hlL hnR.le
  have hnl2 : (n : ℝ) * (l - 1) ≤ n * Nat.log 2 n :=
    mul_le_mul_of_nonneg_left (by linarith) hnR.le
  have hden : 0 < (n : ℝ) * l := mul_pos hnR hlpos
  rw [mul_div_assoc, ← hl']
  constructor
  · rw [le_div_iff₀ hden]
    linarith
  · rw [div_le_iff₀ hden]
    linarith

end H13A080277

open OMA.S_oeis_a080277 H13A080277 in
theorem OMA.solution : type_of% @OMA.S_oeis_a080277.main := by
  have hlog2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hl : Filter.Tendsto (fun n : ℕ => Real.log n / Real.log 2) Filter.atTop Filter.atTop :=
    (Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop).atTop_div_const hlog2
  have hinv : Filter.Tendsto (fun n : ℕ => (Real.log n / Real.log 2)⁻¹) Filter.atTop (nhds 0) :=
    tendsto_inv_atTop_zero.comp hl
  have hup : Filter.Tendsto (fun n : ℕ => 1 + (Real.log n / Real.log 2)⁻¹) Filter.atTop
      (nhds 1) := by
    have h := (tendsto_const_nhds : Filter.Tendsto (fun _ : ℕ => (1 : ℝ)) Filter.atTop
      (nhds 1)).add hinv
    rwa [add_zero] at h
  have hlow : Filter.Tendsto (fun n : ℕ => 1 - 2 * (Real.log n / Real.log 2)⁻¹) Filter.atTop
      (nhds 1) := by
    have h := (tendsto_const_nhds : Filter.Tendsto (fun _ : ℕ => (1 : ℝ)) Filter.atTop
      (nhds 1)).sub (hinv.const_mul 2)
    rwa [mul_zero, sub_zero] at h
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le' hlow hup ?_ ?_
  · filter_upwards [Filter.eventually_ge_atTop 2] with n hn
    exact (pointwise n hn).1
  · filter_upwards [Filter.eventually_ge_atTop 2] with n hn
    exact (pointwise n hn).2
