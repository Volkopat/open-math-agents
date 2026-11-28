import OMAReductions.R_Erdos5_erdos_5_variants_banks_freiberg_maynard_R1

/-!
Chebyshev's lower bound for the prime-counting function gives
p_n ≤ 8 n log p_n for n ≥ 1. Taking logs and dividing by log p_n
squeezes the reciprocal ratio log n / log p_n between 1 and a lower
bound that differs from 1 by O(log log p_n / log p_n).

This shortens the normalization proof submitted by @JamesSlash, adapted
from @ishaanzee's PR #4324.
-/

open Filter Real
open scoped Topology

private lemma log_nth_prime_index (n : ℕ) (hn : 1 ≤ n) :
    log (Nat.nth Nat.Prime n) ≤ log (n : ℝ) + log 8 + log (log (Nat.nth Nat.Prime n)) := by
  let p := Nat.nth Nat.Prime n
  change log (p : ℝ) ≤ _
  have hp : (2 : ℝ) ≤ p := by exact_mod_cast (Nat.prime_nth_prime n).two_le
  have hn' : (1 : ℝ) ≤ n := by exact_mod_cast hn
  have hlog : 0 < log (p : ℝ) := log_pos (by linarith)
  have hcount : Nat.primeCounting p = n + 1 := by
    rw [Nat.primeCounting, Nat.primeCounting', Nat.count_succ, ← Nat.primeCounting',
      Nat.primeCounting'_nth_eq, if_pos (Nat.prime_nth_prime n)]
  have hcheb := Chebyshev.pi_ge p
  rw [hcount, div_le_iff₀ hlog] at hcheb
  push_cast at hcheb
  have hadd : log ((p : ℝ) + 1) ≤ log 2 + log (p : ℝ) := by
    rw [← log_mul (by norm_num : (2 : ℝ) ≠ 0) (by positivity)]
    exact log_le_log (by positivity) (by linarith)
  have hlog₂ : log (2 : ℝ) ≤ log (p : ℝ) := log_le_log (by norm_num) hp
  have hhalf : (1 / 2 : ℝ) ≤ log 2 := by
    have h := log_le_sub_one_of_pos (show 0 < (2 : ℝ)⁻¹ by norm_num)
    rw [log_inv] at h
    norm_num at h
    linarith
  have hbound : (p : ℝ) ≤ (8 * n) * log (p : ℝ) := by
    nlinarith [mul_le_mul_of_nonneg_left hhalf (show (0 : ℝ) ≤ p by positivity),
      mul_le_mul_of_nonneg_right (show (n : ℝ) + 3 ≤ 4 * n by linarith) hlog.le]
  calc
    log (p : ℝ) ≤ log ((8 * n) * log (p : ℝ)) := log_le_log (by positivity) hbound
    _ = _ := by rw [log_mul (by positivity) hlog.ne', log_mul (by norm_num) (by positivity)]
                ring

theorem OMA.solution : OMA.R_Erdos5_erdos_5_variants_banks_freiberg_maynard_R1.H2 := by
  unfold OMA.R_Erdos5_erdos_5_variants_banks_freiberg_maynard_R1.H2
  let p (n : ℕ) : ℝ := Nat.nth Nat.Prime n
  have hle (n : ℕ) : (n : ℝ) ≤ p n := by
    change (n : ℝ) ≤ (Nat.nth Nat.Prime n : ℝ)
    exact_mod_cast (Nat.le_add_right n 2).trans (Nat.add_two_le_nth_prime n)
  have hlogPos (n : ℕ) : 0 < log (p n) := by
    change 0 < log (Nat.nth Nat.Prime n : ℝ)
    exact log_pos (by exact_mod_cast (Nat.prime_nth_prime n).one_lt)
  have hp : Tendsto p atTop atTop := tendsto_atTop_mono hle tendsto_natCast_atTop_atTop
  have hlog : Tendsto (fun n ↦ log (p n)) atTop atTop := tendsto_log_atTop.comp hp
  have herr : Tendsto (fun n ↦ (log 8 + log (log (p n))) / log (p n)) atTop (𝓝 0) := by
    have hc := (tendsto_const_nhds (x := log 8)).div_atTop hlog
    have hsmall := isLittleO_log_id_atTop.tendsto_div_nhds_zero.comp hlog
    simpa only [Function.comp_apply, id_eq, ← add_div, add_zero] using hc.add hsmall
  have hinv : Tendsto (fun n : ℕ ↦ log (n : ℝ) / log (p n)) atTop (𝓝 1) := by
    have hl : Tendsto (fun n ↦ 1 - (log 8 + log (log (p n))) / log (p n)) atTop (𝓝 1) := by
      simpa only [sub_zero] using (tendsto_const_nhds (x := (1 : ℝ))).sub herr
    refine tendsto_of_tendsto_of_tendsto_of_le_of_le' hl tendsto_const_nhds ?_ ?_
    · filter_upwards [eventually_ge_atTop 2] with n hn
      have hpos := hlogPos n
      rw [le_div_iff₀ hpos, sub_mul, one_mul, div_mul_cancel₀ _ hpos.ne']
      linarith [log_nth_prime_index n (by omega)]
    · filter_upwards [eventually_ge_atTop 2] with n hn
      have hpos := hlogPos n
      have hn' : (1 : ℝ) < n := by exact_mod_cast hn
      rw [div_le_iff₀ hpos, one_mul]
      exact log_le_log (by linarith) (hle n)
  simpa only [inv_div, inv_one, p] using hinv.inv₀ one_ne_zero
