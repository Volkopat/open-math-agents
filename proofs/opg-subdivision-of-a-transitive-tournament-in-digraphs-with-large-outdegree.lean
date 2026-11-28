import OMAStatements.S_opg_subdivision_of_a_transitive_tournament_in_digraphs_with_large_outdegree

/-- Even a one-vertex subdivision requires a branch vertex, whereas the
pointwise outdegree condition holds for every threshold on the empty graph. -/
theorem OMA.disproof :
    ¬ (type_of% @OMA.S_opg_subdivision_of_a_transitive_tournament_in_digraphs_with_large_outdegree.main) := by
  intro h
  obtain ⟨_, hf⟩ := h 1
  obtain ⟨branch, _⟩ := hf Empty (fun _ _ => False) (fun v => v.elim) (fun v => v.elim)
  exact (branch 0).elim
