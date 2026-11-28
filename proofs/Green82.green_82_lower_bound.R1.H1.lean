import OMAReductions.R_Green82_green_82_lower_bound_R1

open Filter Real Asymptotics
open scoped Topology

theorem OMA.solution : OMA.R_Green82_green_82_lower_bound_R1.H1 := by
  intro c hc
  let x (n : ℕ) := log (log (n : ℝ))
  let y (n : ℕ) := log (x n)
  let o (n : ℕ) := (log (y n) - log c) / y n
  have hx : Tendsto x atTop atTop :=
    tendsto_log_atTop.comp (tendsto_log_atTop.comp tendsto_natCast_atTop_atTop)
  have hy : Tendsto y atTop atTop := tendsto_log_atTop.comp hx
  refine ⟨o, (isLittleO_one_iff ℝ).mpr ?_, ?_⟩
  · have hlog : Tendsto (fun n => log (y n) / y n) atTop (𝓝 0) :=
      isLittleO_log_id_atTop.tendsto_div_nhds_zero.comp hy
    simpa only [o, sub_div, sub_zero] using hlog.sub (hy.const_div_atTop (log c))
  · filter_upwards [hx.eventually (eventually_gt_atTop (0 : ℝ)),
      hy.eventually (eventually_ge_atTop c)] with n hn hcny
    have hyn : 0 < y n := hc.trans_le hcny
    have ho : 0 ≤ o n := div_nonneg (sub_nonneg.mpr (log_le_log hc hcny)) hyn.le
    change x n ^ (1 - |o n|) ≤ c * x n / y n
    rw [abs_of_nonneg ho, rpow_def_of_pos hn]
    have he : log (x n) * (1 - o n) = log (x n) - log (y n) + log c := by
      change y n * (1 - (log (y n) - log c) / y n) = y n - log (y n) + log c
      field_simp
      <;> ring
    rw [he, exp_add, exp_sub, exp_log hn, exp_log hyn, exp_log hc]
    exact le_of_eq (by ring)
