import OMAStatements.S_oeis_a322600
import Mathlib.Tactic

/-! At n = 16 the numerator contributes 7, but the published homogeneous
recurrence forces the very same coefficient to vanish. This is a discrepancy
in the claimed range and is independent of how the lattices are counted. -/

open OMA.S_oeis_a322600

theorem OMA.disproof : ¬ (type_of% @OMA.S_oeis_a322600.main) := by
  rintro ⟨series, recurrence⟩
  have coefficient := series 16
  have step := recurrence 16 (by decide)
  change a 16 - a 15 - a 14 + a 11 + a 10 + a 9 - a 8 - a 7 - a 6 +
    a 3 + a 2 - a 1 = 7 at coefficient
  change a 16 = a 15 + a 14 - a 11 - a 10 - a 9 + a 8 + a 7 + a 6 -
    a 3 - a 2 + a 1 at step
  omega
