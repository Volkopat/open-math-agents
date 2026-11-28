import OMAStatements.S_oeis_a267515

set_option maxRecDepth 100000 in
theorem OMA.disproof : ¬ (type_of% @OMA.S_oeis_a267515.main) := fun h =>
  absurd (h.1 62 (by decide)) (by decide)
