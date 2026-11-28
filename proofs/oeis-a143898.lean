import OMAStatements.S_oeis_a143898
import Mathlib

open Real OMA.S_oeis_a143898 in
theorem OMA.disproof : ¬ (type_of% @OMA.S_oeis_a143898.main) := by
  intro h
  let K : ℝ := log 1151 / log 95
  have hlog : 0 < log (95 : ℝ) := log_pos (by norm_num)
  have hK : K < 5 / 3 := by
    have h := log_lt_log (show 0 < (1151 : ℝ) ^ (3 : ℕ) by positivity)
      (show (1151 : ℝ) ^ (3 : ℕ) < (95 : ℝ) ^ (5 : ℕ) by norm_num)
    rw [log_pow, log_pow] at h
    change log 1151 / log 95 < 5 / 3
    apply (div_lt_iff₀ hlog).mpr
    norm_num at h
    linarith only [h]
  have h95 : (95 : ℝ) ^ K = 1151 := by
    rw [rpow_def_of_pos (by norm_num : (0 : ℝ) < 95)]
    dsimp [K]
    rw [show log 95 * (log 1151 / log 95) = log 1151 by
      field_simp [ne_of_gt hlog]]
    exact exp_log (by norm_num)
  have hcubes : ((1129 : ℝ) / 1151) ^ (3 : ℕ) <
      (((94 : ℝ) / 95) ^ ((5 : ℝ) / 3)) ^ (3 : ℕ) := by
    rw [← rpow_natCast (((94 : ℝ) / 95) ^ ((5 : ℝ) / 3)) 3,
      ← rpow_mul (by positivity : (0 : ℝ) ≤ 94 / 95)]
    norm_num [show (5 : ℝ) / 3 * (3 : ℝ) = (5 : ℕ) by norm_num, rpow_natCast]
  have hratio : (1129 : ℝ) / 1151 < ((94 : ℝ) / 95) ^ ((5 : ℝ) / 3) := by
    by_contra! hle
    exact (not_lt_of_ge (pow_le_pow_left₀ (by positivity) hle _)) hcubes
  have hratio' := rpow_lt_rpow_of_exponent_gt
    (show (0 : ℝ) < 94 / 95 by norm_num) (show (94 : ℝ) / 95 < 1 by norm_num) hK
  rw [div_rpow (by norm_num : (0 : ℝ) ≤ 94) (by norm_num : (0 : ℝ) ≤ 95) K, h95] at hratio'
  have hlo : (1129 : ℝ) < (94 : ℝ) ^ K :=
    (div_lt_div_iff_of_pos_right (by norm_num : (0 : ℝ) < 1151)).mp (hratio.trans hratio')
  have hpK : PrimeInEveryInterval K := h.1
  obtain ⟨p, hp, hp₁, hp₂⟩ := hpK 94 (by decide)
  change (94 : ℝ) ^ K < (p : ℝ) at hp₁
  have hp₂' : (p : ℝ) < (95 : ℝ) ^ K := by norm_num at hp₂ ⊢; exact hp₂
  rw [h95] at hp₂'
  have hl : 1129 < p := by exact_mod_cast hlo.trans hp₁
  have hu : p < 1151 := by exact_mod_cast hp₂'
  interval_cases p <;> norm_num at hp