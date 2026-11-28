import OMAStatements.S_oeis_a056142

-- The prefixes of 212 concatenate to 212212, yet the digits 1 and 2 differ.
theorem OMA.disproof : ¬ (type_of% @OMA.S_oeis_a056142.main) := by
  intro h
  exact (by decide : 1 ≠ 2) (h 212 (by decide) (by decide) 1 (by decide) 2 (by decide))
