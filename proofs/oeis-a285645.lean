import OMAStatements.S_oeis_a285645

set_option maxRecDepth 100000 in
theorem OMA.disproof : ¬ (type_of% @OMA.S_oeis_a285645.main) := fun h =>
  absurd (h.2.2.2 5 (by decide)) (by decide +kernel)
