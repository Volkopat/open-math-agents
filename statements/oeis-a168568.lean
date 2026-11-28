import Mathlib

/-!
# A168568: Primes p such that the concatenation p||29 is a squared prime

Source: https://oeis.org/A168568

Conjecture (OEIS A168568):
There are infinitely many primes `p` such that the base-10 concatenation
`p || 29 = 100 * p + 29` is the square of a prime number.

Conventions:
- Offset: `1`; first terms: `5, 53, 3329, 4583, 7691, 12611, ...`
  (giving `529 = 23^2`, `5329 = 73^2`, `332929 = 577^2`, ...).
-/

namespace OMA.S_oeis_a168568

/-- The set of primes `p` such that `100 * p + 29` is the square of a prime (OEIS A168568). -/
def S : Set ℕ :=
  {p : ℕ | Nat.Prime p ∧ ∃ q : ℕ, Nat.Prime q ∧ 100 * p + 29 = q ^ 2}

/-- Conjecture: the sequence A168568 is infinite. -/
theorem main : Set.Infinite S := by
  sorry

end OMA.S_oeis_a168568
