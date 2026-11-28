import Mathlib

/-!
# OEIS A168540: Natural numbers n for which 100n^3 + 27 is prime.

Source: https://oeis.org/A168540
Credit: @unserus

OEIS: "It is conjectured that sequence is infinite."
-/

namespace OMA.S_oeis_a168540

/-- The terms of A168540: natural numbers `n` such that `100 n^3 + 27` is prime. -/
def a168540Set : Set ℕ := {n : ℕ | (100 * n ^ 3 + 27).Prime}

/-- A168540 is infinite. -/
theorem main : a168540Set.Infinite := by
  sorry

end OMA.S_oeis_a168540
