import OMAStatements.S_oeis_a175254

theorem OMA.disproof : ¬ (type_of% @OMA.S_oeis_a175254.main) := by
  intro h
  have h2 := h 2 (by norm_num)
  revert h2
  decide
