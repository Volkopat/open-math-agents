import OMAStatements.S_oeis_a071283

theorem OMA.disproof : ¬ (type_of% @OMA.S_oeis_a071283.main) :=
  fun h => absurd (h.2 4) (by decide +kernel)
