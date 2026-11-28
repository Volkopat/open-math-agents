import OMAStatements.S_oeis_a026377

theorem OMA.disproof : ¬ (type_of% @OMA.S_oeis_a026377.main) := fun h =>
  absurd (h 4 le_rfl) (by decide +kernel)
