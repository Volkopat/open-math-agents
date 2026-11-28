import OMAStatements.S_oeis_a168494

theorem OMA.disproof : ¬ (type_of% @OMA.S_oeis_a168494.main) := fun h =>
  absurd (h 6 (by decide)) (by decide)
