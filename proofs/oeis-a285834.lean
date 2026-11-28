import OMAStatements.S_oeis_a285834

theorem OMA.disproof : ¬ (type_of% @OMA.S_oeis_a285834.main) := fun h =>
  absurd (h.2 8 (by decide)) (by decide +kernel)
