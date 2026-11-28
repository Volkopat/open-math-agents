import OMAStatements.S_mo_143188

-- Uses the compact-neighborhood observation from @AkiRA-COM-FP's PR #17629.
-- Mathlib's Riesz theorem supplies the finite-dimensionality contradiction.

open Set Topology

theorem OMA.solution : type_of% @OMA.S_mo_143188.main := by
  intro E _ _ _ _ _ _ _ _ _ _ hDimension ⟨U, hOpen, ⟨e⟩⟩
  have hCompact : IsCompact U := by
    rw [isCompact_iff_compactSpace]
    exact e.compactSpace
  exact hDimension (FiniteDimensional.of_totallyBounded_nhds ℝ
    (hOpen.mem_nhds (e (fun _ => 1)).property) hCompact.totallyBounded)
