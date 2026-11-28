import Mathlib

/-!
# A356110: Numbers k such that k^2 + {1, 3, 7, 13, 31} are all prime

Source: https://oeis.org/A356110

Conjecture (OEIS A356110):
There are infinitely many natural numbers `k` such that `k^2 + 1`, `k^2 + 3`, `k^2 + 7`,
`k^2 + 13`, and `k^2 + 31` are all prime.

Conventions:
- Offset: `1`; first terms: `4, 10, 14290, 43054, ...`.
-/

namespace OMA.S_oeis_a356110

/-- The set of natural numbers `k` such that `k^2 + 1, k^2 + 3, k^2 + 7, k^2 + 13, k^2 + 31`
are all prime (OEIS A356110). -/
def S : Set ℕ :=
  {k : ℕ | Nat.Prime (k ^ 2 + 1) ∧ Nat.Prime (k ^ 2 + 3) ∧ Nat.Prime (k ^ 2 + 7) ∧
    Nat.Prime (k ^ 2 + 13) ∧ Nat.Prime (k ^ 2 + 31)}

/-- Conjecture: the set of terms of OEIS A356110 is infinite. -/
theorem main : Set.Infinite S := by
  sorry

end OMA.S_oeis_a356110
