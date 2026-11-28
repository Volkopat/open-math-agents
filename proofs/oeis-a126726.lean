import OMAStatements.S_oeis_a126726

-- Shorter disproof of OEIS A126726 (counterexample n = 2). This version: @tylerpixel

theorem OMA.disproof : ¬ (type_of% @OMA.S_oeis_a126726.main) :=
  fun h => absurd (h 2 (by decide)) (by decide +kernel)
