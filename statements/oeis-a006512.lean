import Mathlib

/-!
# A006512: Greater of twin primes

Source: https://oeis.org/A006512

Conjecture (Twin Prime Conjecture):
The sequence of primes `p` such that `p - 2` is also prime is infinite.

Conventions:
- Offset: `1`; first terms: `5, 7, 13, 19, 31, 43, 61, 73, 103, 109, ...`.
- Requiring `3 ≤ p` avoids `ℕ` subtraction underflow in `p - 2` (and `p = 2, 3` are not
  greater twin primes since `0` and `1` are not prime).
-/

namespace OMA.S_oeis_a006512

/-- The set of greater members of twin prime pairs (OEIS A006512). -/
def S : Set ℕ :=
  {p : ℕ | 3 ≤ p ∧ Nat.Prime p ∧ Nat.Prime (p - 2)}

/-- Conjecture (Twin Prime Conjecture): there are infinitely many twin prime pairs. -/
theorem main : Set.Infinite S := by
  sorry

end OMA.S_oeis_a006512
