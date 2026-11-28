import Mathlib

/-!
# A302988: Primes p such that p - 3 divides 3^p - 3

Source: https://oeis.org/A302988

Conjecture (OEIS A302988):
There are infinitely many primes `p` such that `p - 3` divides `3^p - 3`.

Conventions:
- Offset: `1`; first terms: `2, 5, 7, 11, 13, 31, 73, 241, 367, 491, 577, ...`.
- We express divisibility in `ℤ` so that `p = 2` (where `2 - 3 = -1 ∣ 6`) is handled
  without truncated subtraction, while `p = 3` (`0 ∣ 24`) is automatically excluded.
-/

namespace OMA.S_oeis_a302988

/-- The set of primes `p` such that `((p : ℤ) - 3) ∣ ((3 : ℤ)^p - 3)` (OEIS A302988). -/
def S : Set ℕ :=
  {p : ℕ | Nat.Prime p ∧ ((p : ℤ) - 3) ∣ ((3 : ℤ) ^ p - 3)}

/-- Conjecture: there are infinitely many primes `p` with `(p - 3) ∣ (3^p - 3)`. -/
theorem main : Set.Infinite S := by
  sorry

end OMA.S_oeis_a302988
