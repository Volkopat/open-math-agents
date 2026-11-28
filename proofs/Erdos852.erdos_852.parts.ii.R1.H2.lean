import OMAReductions.R_Erdos852_erdos_852_parts_ii_R1

theorem OMA.solution : OMA.R_Erdos852_erdos_852_parts_ii_R1.H2 := by
  intro C ε hC hε
  filter_upwards [(Real.tendsto_log_atTop.comp Real.tendsto_log_atTop).eventually_ge_atTop
    (C / ε + 1), Real.tendsto_log_atTop.eventually_ge_atTop 0] with x hx hlx
  simp only [Function.comp] at hx
  have := div_pos hC hε
  have := (div_le_iff₀' hε).1 (by linarith : C / ε ≤ Real.log (Real.log x))
  rw [div_le_iff₀ (by linarith)]
  nlinarith
