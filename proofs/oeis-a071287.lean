import OMAStatements.S_oeis_a071287

theorem OMA.disproof : ¬ (type_of% @OMA.S_oeis_a071287.main) :=
  fun h => absurd (h.2 6) (by decide +kernel)
