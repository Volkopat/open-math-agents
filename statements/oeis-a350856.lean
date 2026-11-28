import Mathlib

/-!
# A350856: Initial members of prime triples (p, p + 2, p + 14)

Source: https://oeis.org/A350856

Conjecture (OEIS A350856, implied by the Hardy-Littlewood k-tuple conjecture):
There are infinitely many primes `p` such that `p + 2` and `p + 14` are also prime.

Conventions:
- Offset: `1`; first terms: `3, 5, 17, 29, 59, 137, 149, 179, 197, 227, ...`.
-/

namespace OMA.S_oeis_a350856

/-- The set of primes `p` such that `p + 2` and `p + 14` are also prime (OEIS A350856). -/
def S : Set ℕ :=
  {p : ℕ | Nat.Prime p ∧ Nat.Prime (p + 2) ∧ Nat.Prime (p + 14)}

/-- Conjecture: there are infinitely many prime triples `(p, p + 2, p + 14)`. -/
theorem main : Set.Infinite S := by
  sorry

end OMA.S_oeis_a350856
