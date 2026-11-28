import OMAReductions.R_Erdos142_erdos_142_variants_lower_R2_H1_R1_H2_R1

open Filter Real

theorem OMA.solution : OMA.R_Erdos142_erdos_142_variants_lower_R2_H1_R1_H2_R1.H2 := by
  intro c η hc hη
  have hL : 0 < log 4 := by positivity
  have H : Tendsto (fun j : ℕ ↦ log (j * log 4)) atTop atTop :=
    tendsto_log_atTop.comp (tendsto_natCast_atTop_atTop.atTop_mul_const hL)
  -- For x = j * log 4, the tail has c * (log x)^η ≥ 2 and is bounded by x⁻².
  refine Summable.of_norm_bounded_eventually_nat
    ((summable_nat_rpow.mpr (show (-2 : ℝ) < -1 by norm_num)).mul_right (log 4 ^ (-2 : ℝ))) ?_
  filter_upwards [((tendsto_rpow_atTop hη).comp H).eventually_ge_atTop (2 / c),
    H.eventually_gt_atTop 0, eventually_gt_atTop 0] with j hj hx hj0
  change 2 / c ≤ log (j * log 4) ^ η at hj
  have hpos : 0 < (j : ℝ) := by exact_mod_cast hj0
  rw [norm_of_nonneg (exp_pos _).le, log_pow, ← mul_rpow hpos.le hL.le,
    rpow_def_of_pos (mul_pos hpos hL), exp_le_exp, rpow_add hx, rpow_one]
  nlinarith only [mul_le_mul_of_nonneg_right ((div_le_iff₀ hc).mp hj) hx.le]
