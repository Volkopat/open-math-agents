import OMAReductions.R_Arxiv_2001_02665_kotzig_conjecture_large_R1_H1_R1

-- Two unordered pairs are equal exactly when the endpoints agree in one of the two orders.

theorem OMA.solution : OMA.R_Arxiv_2001_02665_kotzig_conjecture_large_R1_H1_R1.H2 := by
  intro n T _ h
  obtain ⟨g, hg⟩ := h
  refine ⟨g, fun u₁ v₁ u₂ v₂ h1 h2 h3 => ?_⟩
  rw [Sym2.eq_iff]
  exact hg u₁ v₁ u₂ v₂ h1 h2 h3
