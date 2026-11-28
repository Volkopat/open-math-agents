import Mathlib

/-!
# A302987: Primes p such that p + 3 divides 3^p + 3

Source: https://oeis.org/A302987

Conjecture (OEIS A302987):
There are only finitely many primes `p` such that `p + 3` divides `3^p + 3`.

Conventions:
- Offset: `1`; known terms: `3, 7, 727`.
-/

namespace OMA.S_oeis_a302987

/-- The set of primes `p` such that `(p + 3) ∣ (3^p + 3)` (OEIS A302987). -/
def S : Set ℕ :=
  {p : ℕ | Nat.Prime p ∧ (p + 3) ∣ (3 ^ p + 3)}

/-- Conjecture: the set of primes `p` with `(p + 3) ∣ (3^p + 3)` is finite. -/
theorem main : Set.Finite S := by
  sorry

end OMA.S_oeis_a302987
