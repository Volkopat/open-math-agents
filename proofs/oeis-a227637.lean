import OMAStatements.S_oeis_a227637

set_option maxHeartbeats 400000000 in
theorem OMA.disproof : ¬ (type_of% @OMA.S_oeis_a227637.main) := fun h =>
  absurd (h.2 0) (by decide +kernel)
