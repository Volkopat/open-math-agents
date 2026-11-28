import OMAStatements.S_oeis_a280606

theorem OMA.disproof : ¬ (type_of% @OMA.S_oeis_a280606.main) := fun h =>
  absurd (h.2 6 (by decide)) (by decide +kernel)
