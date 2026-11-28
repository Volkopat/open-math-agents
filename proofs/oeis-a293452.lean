import OMAStatements.S_oeis_a293452

-- At width one the sole site is the sink. The empty run is already stable.
theorem OMA.disproof : ¬ (type_of% @OMA.S_oeis_a293452.main) := by
  intro h
  have e := (h 1 (by decide) 0).mp ⟨[], by change ∀ j : Fin 1, OMA.S_oeis_a293452.initial 1 j < 4; decide, rfl⟩
  exact (by decide : 0 ≠ OMA.S_oeis_a293452.rectangleSum 1) e
