import OMAStatements.S_wp_zarankiewicz_problem

open OMA.S_wp_zarankiewicz_problem

theorem OMA.disproof : ¬ (type_of% @OMA.S_wp_zarankiewicz_problem.main) := by
  intro h
  obtain ⟨E, hFree, _⟩ := (h 1 1 0 0).1
  exact hFree ⟨∅, ∅, rfl, rfl, by simp⟩