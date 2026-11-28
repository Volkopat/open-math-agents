import OMAReductions.R_Erdos852_erdos_852_parts_ii_R1

-- Step Erdos852.erdos_852.parts.ii.R1.H2: hypothesis H2 of reduction Erdos852.erdos_852.parts.ii.R1
-- Credit: @Raimo33

/-! Eventually `log (log x) ≥ C / ε + 1`, so `C ≤ ε * log (log x)`; multiply by `log x ≥ 0`. -/

theorem OMA.solution : OMA.R_Erdos852_erdos_852_parts_ii_R1.H2 := by
  intro C ε hC hε
  have hLL : Filter.Tendsto (fun x : ℝ => Real.log (Real.log x)) Filter.atTop Filter.atTop :=
    Real.tendsto_log_atTop.comp Real.tendsto_log_atTop
  filter_upwards [hLL.eventually_ge_atTop (C / ε + 1),
    Real.tendsto_log_atTop.eventually_ge_atTop 0] with x hx hlx
  have hq : 0 < C / ε := div_pos hC hε
  have hpos : 0 < Real.log (Real.log x) := by linarith
  have h1 : C ≤ ε * Real.log (Real.log x) := by
    have h2 := mul_le_mul_of_nonneg_left hx hε.le
    have h3 : ε * (C / ε) = C := mul_div_cancel₀ C hε.ne'
    nlinarith
  rw [div_le_iff₀ hpos]
  have h4 := mul_le_mul_of_nonneg_left h1 hlx
  nlinarith
