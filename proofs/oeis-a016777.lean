import OMAStatements.S_oeis_a016777

theorem OMA.disproof : ¬ (type_of% @OMA.S_oeis_a016777.main) := fun h =>
  absurd (h 2 {1,2} one_le_two rfl (by decide) (by simp [OMA.S_oeis_a016777.PropP])) (by decide)
