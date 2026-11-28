import OMAStatements.S_oeis_a267514

set_option maxRecDepth 100000 in
theorem OMA.disproof : ¬ (type_of% @OMA.S_oeis_a267514.main) := fun h =>
  absurd (h.1 62 (by decide)) (by decide)
