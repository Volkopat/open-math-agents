import OMAStatements.S_oeis_a281217

theorem OMA.disproof : ¬ (type_of% @OMA.S_oeis_a281217.main) := fun h =>
  absurd (h 1) (by decide +kernel)
