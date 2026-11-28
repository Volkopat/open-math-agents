import OMAStatements.S_oeis_a270088

/- Colin Barker's recurrence is stated for n > 4. The first permitted index
already fails. The same discrepancy is recorded in section 7.2 of
https://aixiv.online/pdf/2611.02474 . This derivation uses the count from the
three-step configuration and three instances of the source's closed form. -/

open OMA.S_oeis_a270088

theorem OMA.disproof : ¬ (type_of% @OMA.S_oeis_a270088.main) := by
  rintro ⟨formula, recurrence, _⟩
  have initial : a 2 = 40 := by decide +kernel
  have h := recurrence 5 (by decide)
  change (a 5 : ℤ) = 7 * (a 4 : ℤ) - 14 * (a 3 : ℤ) + 8 * (a 2 : ℤ) at h
  rw [formula 5 (by decide), formula 4 (by decide), formula 3 (by decide), initial] at h
  norm_num at h
