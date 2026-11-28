import OMAStatements.S_oeis_a190036

set_option maxHeartbeats 0 in
theorem OMA.disproof : ¬ (type_of% @OMA.S_oeis_a190036.main) := fun h =>
  absurd (h.2 1) (by decide +kernel)
