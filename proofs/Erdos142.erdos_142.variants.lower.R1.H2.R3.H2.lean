import OMAReductions.R_Erdos142_erdos_142_variants_lower_R1_H2_R3

-- Step Erdos142.erdos_142.variants.lower.R1.H2.R3.H2: hypothesis H2 of reduction Erdos142.erdos_142.variants.lower.R1.H2.R3
-- Credit: @Raimo33

open Real Filter in
theorem OMA.solution : OMA.R_Erdos142_erdos_142_variants_lower_R1_H2_R3.H2 := by
  intro A C c ε _ _ hc hε
  have hl := tendsto_log_atTop.comp tendsto_natCast_atTop_atTop
  filter_upwards [((tendsto_exp_mul_div_rpow_atTop (A / ε) c hc).comp
    ((tendsto_rpow_atTop hε).comp hl)).eventually_ge_atTop C, hl.eventually_gt_atTop 0] with N h hL
  dsimp at h hL
  rw [← rpow_mul hL.le, mul_div_cancel₀ A hε.ne'] at h
  rwa [neg_mul, exp_neg, mul_inv_le_iff₀ (exp_pos _), div_mul_eq_mul_div, one_mul]
