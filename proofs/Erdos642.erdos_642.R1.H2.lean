import OMAReductions.R_Erdos642_erdos_642_R1

theorem OMA.solution : OMA.R_Erdos642_erdos_642_R1.H2 := by
  intro C hC
  exact Erdos642.isBigO_iff_uniform_edge_bound.mpr ⟨C, hC⟩