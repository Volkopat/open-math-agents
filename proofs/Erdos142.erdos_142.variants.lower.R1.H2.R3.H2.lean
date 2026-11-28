-- Based on the comparison proofs by @596050 (PR 38127) and @jojo259 (PR 37384), following @Raimo33.
import OMAReductions.R_Erdos142_erdos_142_variants_lower_R1_H2_R3

open Real Filter

theorem OMA.solution : OMA.R_Erdos142_erdos_142_variants_lower_R1_H2_R3.H2 := by
  intro A C c ε _ _ hc hε
  simpa [← rpow_mul (log_natCast_nonneg _), mul_div_cancel₀ _ hε.ne', neg_mul, exp_neg, mul_inv_le_iff₀ (exp_pos _), inv_mul_eq_div] using
    ((tendsto_exp_mul_div_rpow_atTop (A / ε) c hc).comp ((tendsto_rpow_atTop hε).comp (tendsto_log_atTop.comp tendsto_natCast_atTop_atTop))).eventually_ge_atTop C
