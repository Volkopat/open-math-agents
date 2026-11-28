import Mathlib

/-!
# A157950: Primes p such that p^8 + 2^8 is prime

Source: https://oeis.org/A157950

Conjecture (OEIS A157950):
There are infinitely many primes `p` such that `p^8 + 2^8` is also prime.

Conventions:
- Offset: `1`; first terms: `13, 137, 223, 331, 389, 491, ...`.
-/

namespace OMA.S_oeis_a157950

/-- The set of primes `p` such that `p^8 + 2^8` is prime (OEIS A157950). -/
def S : Set ℕ :=
  {p : ℕ | Nat.Prime p ∧ Nat.Prime (p ^ 8 + 2 ^ 8)}

/-- Conjecture: there are infinitely many primes `p` with `p^8 + 2^8` prime. -/
theorem main : Set.Infinite S := by
  sorry

end OMA.S_oeis_a157950
