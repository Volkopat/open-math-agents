import Mathlib

/-!
# A004125: Sum of remainders of n mod k, for k = 1, 2, 3, ..., n.

Source: https://oeis.org/A004125
Credit: @rabdelaal

`a n = sum of n % k for k in [1, n]` (OEIS A004125).

OEIS A004125 records Pol's conjecture, proved by Sela Fried (2025): `a(n) - a(n-1) =
2*n - 1 - sigma(n)` for `n >= 2`, where `sigma` is the divisor-sum function. The proof is
a rearrangement of the double sum; we state the conjectured identity.
-/

namespace OMA.S_oeis_a004125

/-- The OEIS A004125 entry: `sum_{k=1}^{n} (n % k)`. -/
def a (n : ℕ) : ℕ := ∑ k ∈ Finset.Icc 1 n, n % k

/-- The total number of proper divisors relevant here: `sigma n`, the sum of divisors
of `n`, as `Nat.divisors.nthSum`-style sigma; Mathlib's `Nat.sigma` is the divisor sum. -/
def σ (n : ℕ) : ℕ := ∑ d ∈ Nat.divisors n, d

/-- Pol's conjecture (proved, Fried 2025): the first difference of A004125 is
`2*n - 1 - sigma(n)` for `n >= 2`. Stated for `n >= 1` with truncated subtraction. -/
theorem main : ∀ n ≥ 2, a n - a (n - 1) = 2 * n - 1 - σ n := by
  sorry

end OMA.S_oeis_a004125
