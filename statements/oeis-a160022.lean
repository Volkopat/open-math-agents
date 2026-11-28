import Mathlib

/-!
# A160022: Primes p such that p^4 + 5^4 + 3^4 is prime

Source: https://oeis.org/A160022

Conjecture (OEIS A160022):
There are infinitely many primes `p` such that `p^4 + 5^4 + 3^4` is also prime.

Conventions:
- Offset: `1`; first terms: `3, 23, 47, 53, 67, 73, 89, 101, 103, 109, ...`.
-/

namespace OMA.S_oeis_a160022

/-- The set of primes `p` such that `p^4 + 5^4 + 3^4` is prime (OEIS A160022). -/
def S : Set ℕ :=
  {p : ℕ | Nat.Prime p ∧ Nat.Prime (p ^ 4 + 5 ^ 4 + 3 ^ 4)}

/-- Conjecture: there are infinitely many primes `p` with `p^4 + 5^4 + 3^4` prime. -/
theorem main : Set.Infinite S := by
  sorry

end OMA.S_oeis_a160022
