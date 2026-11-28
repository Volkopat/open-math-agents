import Mathlib

/-!
# A341665: Primes p such that p^5 - 1 has 8 divisors

Source: https://oeis.org/A341665

Conjecture (OEIS A341665):
There are infinitely many primes `p` such that `p^5 - 1` has exactly `8` positive divisors.

Conventions:
- Offset: `1`; first terms: `7, 23, 83, 227, 263, ...`.
- `(p ^ 5 - 1).divisors.card` counts the exact number of positive divisors `τ(p^5 - 1)`.
-/

namespace OMA.S_oeis_a341665

/-- The set of primes `p` such that `p^5 - 1` has exactly `8` positive divisors
(OEIS A341665). -/
def S : Set ℕ :=
  {p : ℕ | Nat.Prime p ∧ (p ^ 5 - 1).divisors.card = 8}

/-- Conjecture: there are infinitely many primes `p` such that `p^5 - 1` has `8` divisors. -/
theorem main : Set.Infinite S := by
  sorry

end OMA.S_oeis_a341665
