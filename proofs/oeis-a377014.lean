import OMAStatements.S_oeis_a377014

theorem OMA.disproof : ¬ (type_of% @OMA.S_oeis_a377014.main) := by
  intro h
  have h79 := h 79 (by norm_num) (by decide +kernel)
  revert h79
  decide
