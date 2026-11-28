import Mathlib

/-!
# OEIS A352480: four consecutive primes p, q, r, s with A001414(q+r) dividing p+q+r+s

Source: https://oeis.org/A352480
Credit: @unserus

OEIS: "If x is a prime and 2*x-y,2*x-z,2*x+z,2*x+y+32 are consecutive primes with
0 < z < y, then 2*x-y is a term. Thus Dickson's conjecture implies there are
infinitely many terms."

A001414(n) is the sum of the prime factors of `n` with multiplicity (sopfr). The
terms are the primes `p` such that, with `q, r, s` the next three primes after
`p`, `A001414(q + r)` divides `p + q + r + s`. The open statement is that the
sequence is infinite.
-/

namespace OMA.S_oeis_a352480

/-- `b` is the least prime greater than `a`. -/
def IsNextPrime (a b : ℕ) : Prop :=
  b.Prime ∧ a < b ∧ ∀ c, a < c → c < b → ¬ c.Prime

/-- A001414: the sum of the prime factors of `n` with multiplicity. -/
def sopfr (n : ℕ) : ℕ := ∑ p ∈ n.primeFactors, p * n.factorization p

/-- The terms of A352480. -/
def a352480Set : Set ℕ :=
  {p | p.Prime ∧ ∃ q r s, IsNextPrime p q ∧ IsNextPrime q r ∧ IsNextPrime r s ∧
    sopfr (q + r) ∣ p + q + r + s}

/-- A352480 is infinite. -/
theorem main : a352480Set.Infinite := by
  sorry

end OMA.S_oeis_a352480
