import OMAReductions.R_arxiv_2409_19103_R1_H1_R1

theorem OMA.solution : OMA.R_arxiv_2409_19103_R1_H1_R1.H3 := by
  intro G g
  dsimp only
  intro i y h
  exact (h.image _).measure_zero _