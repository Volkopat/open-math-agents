import Mathlib

/-!
# A129962: Primes of the form 2^k + k

Source: https://oeis.org/A129962

Conjecture (OEIS A129962):
There are infinitely many primes of the form `2^k + k`.

Conventions:
- Offset: `1`; first terms: `3, 11, 37, 521, 32783, 549755813927, ...`
  (corresponding to `k = 1, 3, 5, 9, 15, 39, ...`).
-/

namespace OMA.S_oeis_a129962

/-- The set of primes of the form `2^k + k` (OEIS A129962). -/
def S : Set ℕ :=
  {p : ℕ | Nat.Prime p ∧ ∃ k : ℕ, p = 2 ^ k + k}

/-- Conjecture: there are infinitely many primes of the form `2^k + k`. -/
theorem main : Set.Infinite S := by
  sorry

end OMA.S_oeis_a129962
