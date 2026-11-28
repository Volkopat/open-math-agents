import OMAStatements.S_oeis_a103769

theorem OMA.disproof : ¬ (type_of% @OMA.S_oeis_a103769.main) := fun h =>
  absurd (h 4 le_rfl) (by decide +kernel)
