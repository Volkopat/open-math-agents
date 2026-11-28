import Mathlib

/-!
# A054723: Prime exponents of composite Mersenne numbers

Source: https://oeis.org/A054723

Conjecture (OEIS A054723, implied by Dickson's conjecture):
There are infinitely many primes `p` such that the Mersenne number `2^p - 1` is composite.

Conventions:
- Offset: `1`; first terms: `11, 23, 29, 37, 41, 43, 47, 53, 59, 67, ...`.
- Since `p ≥ 2` implies `2^p - 1 ≥ 3`, `¬ Nat.Prime (2 ^ p - 1)` is equivalent to
  `2^p - 1` being composite.
-/

namespace OMA.S_oeis_a054723

/-- The set of primes `p` such that `2^p - 1` is composite (OEIS A054723). -/
def S : Set ℕ :=
  {p : ℕ | Nat.Prime p ∧ ¬ Nat.Prime (2 ^ p - 1)}

/-- Conjecture: there are infinitely many prime exponents `p` for which `2^p - 1` is composite. -/
theorem main : Set.Infinite S := by
  sorry

end OMA.S_oeis_a054723
