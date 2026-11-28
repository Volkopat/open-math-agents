import Mathlib

/-!
# A171771: Primes of the form n^6 - (n + 1)^5

Source: https://oeis.org/A171771

Conjecture (OEIS A171771):
There are infinitely many primes of the form `n^6 - (n + 1)^5`.

Conventions:
- Offset: `1`; first terms: `971, 431441, 838949, 2614691, 6770161, ...`
  (corresponding to `n = 4, 9, 10, 12, 14, ...`).
- We work in `ℤ` for the subtraction `n^6 - (n + 1)^5` to avoid truncated subtraction
  for `n ≤ 3` (where `n^6 < (n + 1)^5`).
-/

namespace OMA.S_oeis_a171771

/-- The set of primes of the form `n^6 - (n + 1)^5` (OEIS A171771). -/
def S : Set ℕ :=
  {p : ℕ | Nat.Prime p ∧ ∃ n : ℕ, (p : ℤ) = (n : ℤ) ^ 6 - ((n : ℤ) + 1) ^ 5}

/-- Conjecture: there are infinitely many primes of the form `n^6 - (n + 1)^5`. -/
theorem main : Set.Infinite S := by
  sorry

end OMA.S_oeis_a171771
