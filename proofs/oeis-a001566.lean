import OMAStatements.S_oeis_a001566
import Mathlib

/-!
# The first quotient is zero

The initial term is 3, so the next term is 7. Subtracting 7 and dividing by
8 gives zero at index 1. In particular, the square 4 divides that quotient.
-/

theorem OMA.disproof : ¬ (type_of% @OMA.S_oeis_a001566.main) := by
  intro h
  have hzero : OMA.S_oeis_a001566.a 1 = 0 := by decide
  exact h.1 1 (by decide) 2 (by decide) (by rw [hzero]; exact dvd_zero _)
