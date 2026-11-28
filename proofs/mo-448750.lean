import OMAStatements.S_mo_448750

-- Problem: MathOverflow 448750, orthogonal complement of an arbitrary intersection of closed subspaces.
-- Proof: let S be the span of the complements Zᗮ. Then Sᗮ is the intersection of the Zᗮᗮ, which is the
-- intersection of the Z since each Z is closed. Taking complements again, (sInf C)ᗮ = Sᗮᗮ = closure S.

theorem OMA.solution : type_of% @OMA.S_mo_448750.main := by
  intro 𝕜 _ H _ _ _ C hC
  have h1 : (⨆ Z ∈ C, Zᗮ)ᗮ = sInf C := by
    simp_rw [← Submodule.iInf_orthogonal]
    rw [sInf_eq_iInf]
    refine iInf_congr fun Z => ?_
    by_cases hZ : Z ∈ C
    · rw [iSup_pos hZ, iInf_pos hZ, Submodule.orthogonal_orthogonal_eq_closure,
        (hC Z hZ).submodule_topologicalClosure_eq]
    · rw [iSup_neg hZ, iInf_neg hZ, Submodule.bot_orthogonal_eq_top]
  rw [← h1, Submodule.orthogonal_orthogonal_eq_closure]
