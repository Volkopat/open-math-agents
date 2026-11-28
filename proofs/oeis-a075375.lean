import OMAStatements.S_oeis_a075375

set_option maxRecDepth 20000 in
theorem OMA.disproof : ¬ (type_of% @OMA.S_oeis_a075375.main) := fun h =>
  absurd (h 169 (by norm_num)) (by decide +kernel)
