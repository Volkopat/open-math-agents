import Mathlib

/-!
# OEIS A168219: Naturals n for which 1 + 10*n^3 is prime.

Source: https://oeis.org/A168219
Credit: @unserus

OEIS: "It is conjectured that sequence is infinite."
-/

namespace OMA.S_oeis_a168219

/-- The terms of A168219: natural numbers `n` such that `1 + 10 n^3` is prime. -/
def a168219Set : Set ℕ := {n : ℕ | (1 + 10 * n ^ 3).Prime}

/-- A168219 is infinite. -/
theorem main : a168219Set.Infinite := by
  sorry

end OMA.S_oeis_a168219
