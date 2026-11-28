import OMAStatements.S_oeis_a168494

open OMA.S_oeis_a168494

-- At n = 6 the left side is 7*830 - 62*32 + 155*32 - 130*7 + 30*2 = 7936.
theorem OMA.disproof : ¬ (type_of% @OMA.S_oeis_a168494.main) := by
  intro h
  exact (by decide : ¬ ((6 : ℤ) + 1) * a 6 + (4 - 11 * (6 : ℤ)) * a (6 - 2) +
    5 * (7 * (6 : ℤ) - 11) * a (6 - 2) + (92 - 37 * (6 : ℤ)) * a (6 - 3) +
    6 * (2 * (6 : ℤ) - 7) * a (6 - 4) = 0) (h 6 (by decide))
