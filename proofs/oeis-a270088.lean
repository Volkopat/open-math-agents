import OMAStatements.S_oeis_a270088

/- Colin Barker's recurrence is stated for n > 4. The first permitted index
already fails. The same discrepancy is recorded in section 7.2 of
https://aixiv.online/pdf/2611.02474 . This derivation uses the count from the
three-step configuration and three instances of the source's closed form. -/

open OMA.S_oeis_a270088

theorem OMA.disproof : ¬ (type_of% @OMA.S_oeis_a270088.main) := by
  rintro ⟨closedForm, recurrence, _⟩
  have h2 : a 2 = 40 := by decide +kernel
  have h3 := closedForm 3 (by decide)
  have h4 := closedForm 4 (by decide)
  have h5 := closedForm 5 (by decide)
  have bad := recurrence 5 (by decide)
  change (a 3 : Int) = 225 at h3
  change (a 4 : Int) = 961 at h4
  change (a 5 : Int) = 3969 at h5
  change (a 5 : Int) = 7 * (a 4 : Int) - 14 * (a 3 : Int) + 8 * (a 2 : Int) at bad
  omega
