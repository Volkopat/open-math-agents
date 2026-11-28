import OMAStatements.S_oeis_a071285

theorem OMA.disproof : ¬ (type_of% @OMA.S_oeis_a071285.main) :=
  fun h => absurd (h.2 5) (by decide +kernel)
