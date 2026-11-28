import Mathlib

/-!
# A129963: Primes of the form 4^k + k

Source: https://oeis.org/A129963

Conjecture (OEIS A129963):
There are infinitely many primes of the form `4^k + k`.

Conventions:
- Offset: `1`; first terms: `5, 67, 262153, 1073741839, ...`
  (corresponding to `k = 1, 3, 9, 15, ...`).
-/

namespace OMA.S_oeis_a129963

/-- The set of primes of the form `4^k + k` (OEIS A129963). -/
def S : Set ℕ :=
  {p : ℕ | Nat.Prime p ∧ ∃ k : ℕ, p = 4 ^ k + k}

/-- Conjecture: there are infinitely many primes of the form `4^k + k`. -/
theorem main : Set.Infinite S := by
  sorry

end OMA.S_oeis_a129963
