import OMAReductions.R_Erdos142_erdos_142_variants_lower_R1_H2_R3

-- Original proof by @Raimo33; direct inequality approach in PR #37384.
-- Use nonnegativity of log of any natural number to avoid a separate eventual condition.

open Real Filter in
theorem OMA.solution : OMA.R_Erdos142_erdos_142_variants_lower_R1_H2_R3.H2 := by
  intro A C c ε _ _ hc hε
  filter_upwards [((tendsto_exp_mul_div_rpow_atTop (A / ε) c hc).comp
    ((tendsto_rpow_atTop hε).comp
      (tendsto_log_atTop.comp tendsto_natCast_atTop_atTop))).eventually_ge_atTop C] with N h
  dsimp at h
  rw [← rpow_mul (log_natCast_nonneg N), mul_div_cancel₀ A hε.ne'] at h
  rwa [neg_mul, exp_neg, mul_inv_le_iff₀ (exp_pos _), one_div_mul_eq_div]
