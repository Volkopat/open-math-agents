import OMAStatements.S_oeis_a128828

set_option maxHeartbeats 8000000 in
set_option maxRecDepth 10000 in
theorem OMA.disproof : ¬ (type_of% @OMA.S_oeis_a128828.main) := fun h =>
  absurd (h 17 (by decide)) (by decide +kernel)
