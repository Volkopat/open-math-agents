import OMAReductions.R_Arxiv_2001_02665_ringel_conjecture_large_R1

theorem OMA.solution : OMA.R_Arxiv_2001_02665_ringel_conjecture_large_R1.H2 := by
  intro n V inst T g
  rw [SimpleGraph.edgeSet_map]
  exact Set.ncard_image_of_injective _ g.sym2Map.injective
