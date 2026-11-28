import Mathlib

/-!
# OEIS A343413: Primes p such that 2*p+1+A001414(p+1) is prime

Source: https://oeis.org/A343413
Credit: @unserus

OEIS: "Includes 6*q-1 where q, 6*q-1 and 13*q+4 are prime; Dickson's conjecture
implies there are infinitely many such q."

A001414(n) is the sum of the prime factors of `n` counted with multiplicity
(sopfr), written `∑ p ∈ n.primeFactors, p * n.factorization p`. The terms are
the primes `p` with `2p + 1 + A001414(p + 1)` prime. The open statement is that
the sequence is infinite.
-/

namespace OMA.S_oeis_a343413

/-- A001414(n): the sum of the prime factors of `n` with multiplicity. -/
def sopfr (n : ℕ) : ℕ := ∑ p ∈ n.primeFactors, p * n.factorization p

/-- The terms of A343413. -/
def a343413Set : Set ℕ := {p | p.Prime ∧ (2 * p + 1 + sopfr (p + 1)).Prime}

/-- A343413 is infinite. -/
theorem main : a343413Set.Infinite := by
  sorry

end OMA.S_oeis_a343413
