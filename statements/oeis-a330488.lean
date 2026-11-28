import Mathlib

/-!
# OEIS A330488: Primes p with p+2 prime and p + A001414(p+1) + (p+2) prime

Source: https://oeis.org/A330488
Credit: @unserus

OEIS (A330488): "If q, 18*q-1, 18*q+1 and 37*q+8 are prime, then 18*q-1 is in the
sequence. Dickson's conjecture implies that there are infinitely many such q, and
thus that this sequence is infinite."

A001414(n) is the sum of the prime factors of `n` with multiplicity (sopfr). The
terms are the primes `p` such that `p + 2` is prime and
`p + A001414(p + 1) + (p + 2)` is prime. The open statement is that the
sequence is infinite.
-/

namespace OMA.S_oeis_a330488

/-- A001414: the sum of the prime factors of `n` with multiplicity. -/
def sopfr (n : ℕ) : ℕ := ∑ p ∈ n.primeFactors, p * n.factorization p

/-- The terms of A330488. -/
def a330488Set : Set ℕ :=
  {p | p.Prime ∧ (p + 2).Prime ∧ (p + sopfr (p + 1) + (p + 2)).Prime}

/-- A330488 is infinite. -/
theorem main : a330488Set.Infinite := by
  sorry

end OMA.S_oeis_a330488
