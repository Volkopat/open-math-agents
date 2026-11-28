import Mathlib

/-!
# A057002: Numbers n such that n^1024 + 1 is prime (generalized Fermat primes)

Source: https://oeis.org/A057002

Conjecture (OEIS A057002, implied by Bunyakovsky's conjecture):
There are infinitely many positive integers `n` such that `n^1024 + 1` is prime.

Conventions:
- Offset: `1`; first terms: `1, 108, 128, 134, ...` (`1^1024 + 1 = 2` is prime).
-/

namespace OMA.S_oeis_a057002

/-- The set of positive integers `n` such that `n^1024 + 1` is prime (OEIS A057002). -/
def S : Set ℕ :=
  {n : ℕ | 1 ≤ n ∧ Nat.Prime (n ^ 1024 + 1)}

/-- Conjecture: there are infinitely many positive integers `n` with `n^1024 + 1` prime. -/
theorem main : Set.Infinite S := by
  sorry

end OMA.S_oeis_a057002
