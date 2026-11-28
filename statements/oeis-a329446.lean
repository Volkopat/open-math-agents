import Mathlib

/-!
# OEIS A329446: p mod A001414((p+q)/2) and q mod A001414((p+q)/2) prime

Source: https://oeis.org/A329446
Credit: @unserus

OEIS: "If v is prime such that v-26, v-24, 6*v-1 and 6*v+1 are prime, then 6*v-1
is in the sequence. Dickson's conjecture implies there are infinitely many terms
of this form."

A001414(n) is the sum of the prime factors of `n` with multiplicity (sopfr). The
terms are the odd primes `p` such that, with `q` the next prime after `p` and
`s = A001414((p + q) / 2)`, both `p % s` and `q % s` are prime (`p + q` is even
for odd `p`, so the division is exact). The open statement is that the sequence
is infinite.
-/

namespace OMA.S_oeis_a329446

/-- `b` is the least prime greater than `a`. -/
def IsNextPrime (a b : ℕ) : Prop :=
  b.Prime ∧ a < b ∧ ∀ c, a < c → c < b → ¬ c.Prime

/-- A001414: the sum of the prime factors of `n` with multiplicity. -/
def sopfr (n : ℕ) : ℕ := ∑ p ∈ n.primeFactors, p * n.factorization p

/-- The terms of A329446. -/
def a329446Set : Set ℕ :=
  {p | p.Prime ∧ Odd p ∧ ∃ q, IsNextPrime p q ∧
    (p % sopfr ((p + q) / 2)).Prime ∧ (q % sopfr ((p + q) / 2)).Prime}

/-- A329446 is infinite. -/
theorem main : a329446Set.Infinite := by
  sorry

end OMA.S_oeis_a329446
