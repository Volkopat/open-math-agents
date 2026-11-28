import OMAReductions.R_Erdos102_erdos_102_R1

/-! The upstream API lemma `Erdos102.tendsto_h_iff`, right to left. -/

theorem OMA.solution : OMA.R_Erdos102_erdos_102_R1.H2 :=
  fun c h => (Erdos102.tendsto_h_iff c).mpr h
