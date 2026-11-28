import Mathlib

/-!
# A120227: Numbers k such that 5 + k and 5*k + 1 are prime

Source: https://oeis.org/A120227

Conjecture (OEIS A120227, implied by Dickson's conjecture):
There are infinitely many natural numbers `k` such that both `5 + k` and `5 * k + 1` are prime.

Conventions:
- Offset: `1`; first terms: `2, 6, 8, 12, 14, 26, 36, 38, 42, 48, ...`.
-/

namespace OMA.S_oeis_a120227

/-- The set of natural numbers `k` such that `5 + k` and `5 * k + 1` are both prime
(OEIS A120227). -/
def S : Set ℕ :=
  {k : ℕ | Nat.Prime (5 + k) ∧ Nat.Prime (5 * k + 1)}

/-- Conjecture: there are infinitely many `k` such that `5 + k` and `5 * k + 1` are prime. -/
theorem main : Set.Infinite S := by
  sorry

end OMA.S_oeis_a120227
