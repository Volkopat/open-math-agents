import OMAStatements.S_oeis_a160845

theorem OMA.disproof : ¬ (type_of% @OMA.S_oeis_a160845.main) := fun h =>
  absurd (h.2 1) (by decide +kernel)
