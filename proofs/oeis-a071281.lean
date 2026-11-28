import OMAStatements.S_oeis_a071281

theorem OMA.disproof : ¬ (type_of% @OMA.S_oeis_a071281.main) := by
  rintro h
  exact absurd (h.2 3) (by decide)
