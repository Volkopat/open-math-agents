import Mathlib

/-!
# A066436: Primes of the form 2*n^2 - 1

Source: https://oeis.org/A066436

Conjecture (OEIS A066436):
There are infinitely many primes of the form `2 * n^2 - 1`.

Conventions:
- Offset: `1` (terms `7, 17, 31, 71, 97, 127, 199, 241, ...` for `n = 2, 3, 4, 6, 7, 8, ...`).
- For `n ≥ 1`, `2 * n^2 ≥ 2`, so natural-number subtraction `2 * n^2 - 1` is exact.
-/

namespace OMA.S_oeis_a066436

/-- The set of primes of the form `2 * n^2 - 1` with `n ≥ 1` (OEIS A066436). -/
def S : Set ℕ :=
  {p : ℕ | Nat.Prime p ∧ ∃ n : ℕ, 1 ≤ n ∧ p = 2 * n ^ 2 - 1}

/-- Conjecture: there are infinitely many primes of the form `2 * n^2 - 1`. -/
theorem main : Set.Infinite S := by
  sorry

end OMA.S_oeis_a066436
