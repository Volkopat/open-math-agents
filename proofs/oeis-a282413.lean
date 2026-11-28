import OMAStatements.S_oeis_a282413
import Mathlib

open OMA.S_oeis_a282413 (a)

/-- The odd-index values and the recurrence are incompatible at index five. -/
theorem OMA.disproof : ¬ (type_of% @OMA.S_oeis_a282413.main) := by
  rintro ⟨_, oddTerms, recurrence, _⟩
  have one : a 1 = 1 := by decide +kernel
  have three := oddTerms 3 (by decide) (by decide)
  have five := oddTerms 5 (by decide) (by decide)
  have atFive := recurrence 5 (by decide)
  change (a 5 : ℤ) = 5 * (a 3 : ℤ) - 4 * (a 1 : ℤ) at atFive
  norm_num [one, three, five] at atFive
