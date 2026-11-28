import OMAStatements.S_oeis_a330700

theorem OMA.disproof : ¬ (type_of% @OMA.S_oeis_a330700.main) := fun h =>
  absurd (h 2 (by norm_num)) (by decide +kernel)
