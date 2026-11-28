import OMAStatements.S_oeis_a326390

theorem OMA.disproof : ¬ (type_of% @OMA.S_oeis_a326390.main) := fun h =>
  absurd (h.2.2 5 (by decide)) (by decide +kernel)
