import Mathlib

/-!
# OEIS A160031: Primes p such that p^4 + 2*3^4 is prime.

Source: https://oeis.org/A160031
Credit: @unserus

OEIS: "It is conjectured that the sequence is infinite."
-/

namespace OMA.S_oeis_a160031

/-- The terms of A160031: primes `p` such that `p^4 + 2*3^4` is prime. -/
def a160031Set : Set ℕ := {p : ℕ | p.Prime ∧ (p ^ 4 + 2 * 3 ^ 4).Prime}

/-- A160031 is infinite. -/
theorem main : a160031Set.Infinite := by
  sorry

end OMA.S_oeis_a160031
