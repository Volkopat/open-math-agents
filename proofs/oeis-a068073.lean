import OMAStatements.S_oeis_a068073
open OMA.S_oeis_a068073 in
theorem OMA.disproof : ¬ (type_of% @OMA.S_oeis_a068073.main) := by
  intro h
  have := h 3
  norm_num [a, a000120, a001045, mul_comm Complex.I] at this
