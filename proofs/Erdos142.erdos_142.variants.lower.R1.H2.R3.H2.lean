import OMAReductions.R_Erdos142_erdos_142_variants_lower_R1_H2_R3

/-! Taking logarithms reduces the goal to the fact that log x grows more
slowly than x^ε. Once x ≥ C, a single extra log x absorbs the constant. -/

open Filter Real in
theorem OMA.solution : OMA.R_Erdos142_erdos_142_variants_lower_R1_H2_R3.H2 := by
  intro A C c ε _ hC hc hε
  refine (tendsto_log_atTop.comp tendsto_natCast_atTop_atTop).eventually
    (p := fun x => C * exp (-c*x^ε) ≤ 1/x^A) ?_
  filter_upwards [((isLittleO_log_rpow_atTop hε).const_mul_left (A+1)).bound hc,
    eventually_ge_atTop C] with x h hx
  have pos := hC.trans_le hx
  replace h := (le_abs_self _).trans h
  rw [norm_of_nonneg (by positivity)] at h
  rw [← exp_log hC, ← exp_add, rpow_def_of_pos pos A, one_div, ← exp_neg, exp_le_exp]
  linarith [log_le_log hC hx]
