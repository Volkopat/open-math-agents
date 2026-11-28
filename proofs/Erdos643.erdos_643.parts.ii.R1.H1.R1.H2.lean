import OMAReductions.R_Erdos643_erdos_643_parts_ii_R1_H1_R1

theorem OMA.solution : OMA.R_Erdos643_erdos_643_parts_ii_R1_H1_R1.H2 := fun _ H _ h =>
  (h H subset_rfl).trans ((Finset.card_filter_le _ _).trans (by simp))
