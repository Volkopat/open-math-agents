import Mathlib

/-!
# OEIS A158477: Primes p with property that Q(p) = p^32+2^32 is prime

Source: https://oeis.org/A158477
Credit: @unserus

OEIS: "It is conjectured that sequence a(n) is infinite."

The terms are the primes `p` such that `p^32 + 2^32` is prime. The conjecture is
that there are infinitely many such primes.
-/

namespace OMA.S_oeis_a158477

/-- The terms of A158477. -/
def a158477Set : Set ℕ := {p | p.Prime ∧ (p ^ 32 + 2 ^ 32).Prime}

/-- A158477 is infinite. -/
theorem main : a158477Set.Infinite := by
  sorry

end OMA.S_oeis_a158477
