import OMAStatements.S_oeis_a288925

theorem OMA.disproof : ¬ (type_of% @OMA.S_oeis_a288925.main) := fun h =>
  absurd (h 3) (by decide +kernel)
