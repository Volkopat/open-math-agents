import OMAStatements.S_oeis_a267160

open OMA.S_oeis_a267160

theorem OMA.disproof : ¬ (type_of% @OMA.S_oeis_a267160.main) := by
  intro h
  have bad := h.1 12 (by decide)
  change (19 : ℚ) = 13 + 11 - 6 at bad
  norm_num at bad
