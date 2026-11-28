import OMAStatements.S_oeis_a270222

theorem OMA.disproof : ¬ (type_of% @OMA.S_oeis_a270222.main) := fun h =>
  absurd (h.2.1 0) (by decide +kernel)
