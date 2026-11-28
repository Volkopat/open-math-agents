import Mathlib

/-!
# OEIS A160440: cousin primes (p, p+4) in different centuries

Source: https://oeis.org/A160440
Credit: @unserus

OEIS: "Sequence is probably infinite." and (Robert Israel, Mar 28 2023):
"Dickson's conjecture implies there are infinitely many pairs of primes
(100*k-3, 100*k+1) and infinitely many pairs of primes (100*k-1, 100*k+3)."

The terms are the primes `p` such that `p + 4` is prime (cousin primes) and
`p`, `p + 4` lie in different centuries, i.e. `p / 100 ≠ (p + 4) / 100`
(natural-number division). The conjecture is that there are infinitely many.
-/

namespace OMA.S_oeis_a160440

/-- The terms of A160440. -/
def a160440Set : Set ℕ :=
  {p | p.Prime ∧ (p + 4).Prime ∧ p / 100 ≠ (p + 4) / 100}

/-- A160440 is infinite. -/
theorem main : a160440Set.Infinite := by
  sorry

end OMA.S_oeis_a160440
