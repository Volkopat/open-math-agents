import OMAStatements.S_oeis_a319927

theorem OMA.disproof : ¬ (type_of% @OMA.S_oeis_a319927.main) := fun h =>
  absurd (h 9216 (by unfold OMA.S_oeis_a319927.member; decide +kernel) 1) (by decide +kernel)
