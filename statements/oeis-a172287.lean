import Mathlib

/-!
# OEIS A172287: Primes p such that exactly one of 2p-3 and 3p-2 is prime.

Source: https://oeis.org/A172287
Credit: @unserus

OEIS (R. Israel): "Dickson's conjecture implies that there are infinitely many terms."
The open statement is that the sequence is infinite. The definition follows the title,
`2p - 3` and `3p - 2`, which reproduces the listed data (`17`: `31` prime, `49` not); a comment
in the entry writes `2*a(n)+3` and `3*a(n)+2` instead, which does not match the data.
For a prime `p ≥ 2`, `2p - 3 ≥ 1`, so the subtraction in `ℕ` is exact.
-/

namespace OMA.S_oeis_a172287

/-- The terms of A172287: primes `p` such that exactly one of `2p - 3`, `3p - 2` is prime. -/
def a172287Set : Set ℕ := {p : ℕ | p.Prime ∧ Xor' (2 * p - 3).Prime (3 * p - 2).Prime}

/-- A172287 is infinite. -/
theorem main : a172287Set.Infinite := by
  sorry

end OMA.S_oeis_a172287
