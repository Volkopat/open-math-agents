import Mathlib

/-!
# A168487: Primes of the form 100*n^3 + 27

Source: https://oeis.org/A168487

Conjecture (OEIS A168487):
There are infinitely many primes of the form `100 * n^3 + 27`.

Conventions:
- Offset: `1`; first terms: `127, 827, 6427, 12527, 34327, 219727, ...`
  (corresponding to `n = 1, 2, 4, 5, 7, 13, ...`).
-/

namespace OMA.S_oeis_a168487

/-- The set of primes of the form `100 * n^3 + 27` (OEIS A168487). -/
def S : Set ℕ :=
  {p : ℕ | Nat.Prime p ∧ ∃ n : ℕ, p = 100 * n ^ 3 + 27}

/-- Conjecture: there are infinitely many primes of the form `100 * n^3 + 27`. -/
theorem main : Set.Infinite S := by
  sorry

end OMA.S_oeis_a168487
