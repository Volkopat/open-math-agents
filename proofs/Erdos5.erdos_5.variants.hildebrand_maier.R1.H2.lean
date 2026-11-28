import OMAReductions.R_Erdos5_erdos_5_variants_hildebrand_maier_R1

open Real
-- Step Erdos5.erdos_5.variants.hildebrand_maier.R1.H2: hypothesis H2 of reduction Erdos5.erdos_5.variants.hildebrand_maier.R1
-- Credit: @loremcdmx
-- H2 := ∀ᶠ n : ℕ in atTop, 0 < log n ∧     log n ≤ log (Nat.nth Nat.Prime n) ∧ log (Nat.nth Nat.Prime n) ≤ 2 * log n

namespace OMA.Aux

open Filter Real

lemma key (m : ℕ) (hm : 16 ≤ m) : Nat.nth Nat.Prime m ≤ m ^ 2 := by
  have hm' : (16:ℝ) ≤ m := by exact_mod_cast hm
  have hpi := Chebyshev.pi_ge (m ^ 2)
  have hlogm : 0 < log m := log_pos (by linarith)
  have hl2 : log (((m ^ 2 : ℕ) : ℝ)) = 2 * log m := by
    push_cast; rw [log_pow]; norm_num
  have h2 := log_two_gt_d9
  have hA : log (m : ℝ) ≤ m / 8 + 3 := by
    have h8 : log ((m:ℝ) / 8) ≤ m / 8 - 1 := log_le_sub_one_of_pos (by linarith)
    rw [log_div (by linarith) (by norm_num)] at h8
    have : log 8 = 3 * log 2 := by
      rw [show (8:ℝ) = 2 ^ 3 by norm_num, log_pow]; norm_num
    have h2' := log_two_lt_d9
    linarith
  have h2' := log_two_lt_d9
  have hB : log (((m ^ 2 : ℕ) : ℝ) + 1) ≤ log 2 + 2 * log m := by
    have e : log (2 * (m:ℝ) ^ 2) = log 2 + 2 * log m := by
      rw [log_mul (by norm_num) (by positivity), log_pow]; norm_num
    rw [← e]
    apply log_le_log (by positivity)
    push_cast; nlinarith
  have hm0 : (0:ℝ) ≤ m := by linarith
  have h3 : (m:ℝ) * log m ≤ (m:ℝ) * (m / 8 + 3) := mul_le_mul_of_nonneg_left hA hm0
  have h4 : (m:ℝ)^2 * 0.69 ≤ (m:ℝ)^2 * log 2 := mul_le_mul_of_nonneg_left (by linarith) (by positivity)
  have hlt : (m : ℝ) < (((m ^ 2 : ℕ) : ℝ) * log 2 - log (((m ^ 2 : ℕ) : ℝ) + 1)) / log (((m ^ 2 : ℕ) : ℝ)) := by
    rw [hl2, lt_div_iff₀ (by linarith)]
    push_cast at hB ⊢
    nlinarith
  have hcnt : (m : ℝ) < (Nat.primeCounting (m ^ 2) : ℝ) := lt_of_lt_of_le hlt hpi
  have hcnt' : m < Nat.primeCounting (m ^ 2) := by exact_mod_cast hcnt
  have := Nat.nth_lt_of_lt_count (p := Nat.Prime) (n := m ^ 2 + 1) (k := m) hcnt'
  omega

end OMA.Aux

open Filter Real in
theorem OMA.solution : OMA.R_Erdos5_erdos_5_variants_hildebrand_maier_R1.H2 := by
  unfold OMA.R_Erdos5_erdos_5_variants_hildebrand_maier_R1.H2
  filter_upwards [eventually_ge_atTop 16] with n hn
  have hn' : (16:ℝ) ≤ n := by exact_mod_cast hn
  have hpos : 0 < log n := log_pos (by linarith)
  have hle : n ≤ Nat.nth Nat.Prime n := by
    have := Nat.add_two_le_nth_prime n; omega
  have hk := OMA.Aux.key n hn
  refine ⟨hpos, ?_, ?_⟩
  · exact log_le_log (by linarith) (by exact_mod_cast hle)
  · have hp : (0:ℝ) < Nat.nth Nat.Prime n := by
      have : (0:ℕ) < Nat.nth Nat.Prime n := by omega
      exact_mod_cast this
    calc log (Nat.nth Nat.Prime n) ≤ log ((n:ℝ) ^ 2) :=
          log_le_log hp (by exact_mod_cast hk)
      _ = 2 * log n := by rw [log_pow]; norm_num
