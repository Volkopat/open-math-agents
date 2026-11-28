import Mathlib

/-!
# OEIS A343418: Primes that occur in A343416

Source: https://oeis.org/A343418
Credit: @unserus

OEIS: "If p, 6*p-1 and 19*p+4 are prime, then 19*p+4 = A343416(6*p-1) is a term.
Dickson's conjecture implies that there are infinitely many such terms."

A343416(n) = A001414(n) + A000203(n) + A001414(A000203(n)) + A000203(A001414(n))
for `n ≥ 1`, where A001414 = sopfr (sum of prime factors with multiplicity,
`sopfr 1 = 0`) and A000203 = σ (sum of divisors, `ArithmeticFunction.sigma 1`,
with `σ 0 = 0`, which gives A343416(1) = 1 as listed). The terms of A343418 are
the primes equal to A343416(n) for some `n ≥ 1`. The open statement is that
there are infinitely many.
-/

namespace OMA.S_oeis_a343418

/-- A001414: the sum of the prime factors with multiplicity. -/
def sopfr (n : ℕ) : ℕ := ∑ p ∈ n.primeFactors, p * n.factorization p

/-- A000203: the sum of divisors. -/
abbrev sigma (n : ℕ) : ℕ := ArithmeticFunction.sigma 1 n

/-- A343416(n). -/
def a343416 (n : ℕ) : ℕ := sopfr n + sigma n + sopfr (sigma n) + sigma (sopfr n)

/-- The terms of A343418: primes that are values of A343416. -/
def a343418Set : Set ℕ := {v | v.Prime ∧ ∃ n, 1 ≤ n ∧ a343416 n = v}

/-- A343418 is infinite. -/
theorem main : a343418Set.Infinite := by
  sorry

end OMA.S_oeis_a343418
