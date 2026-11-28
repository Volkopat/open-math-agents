import OMAStatements.S_oeis_a230168

-- A prime one below a positive multiple of five must be odd.
theorem OMA.solution : type_of% @OMA.S_oeis_a230168.main := by
  intro n hp
  have := hp.eq_two_or_odd
  omega
