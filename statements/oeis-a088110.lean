import Mathlib

/-!
# A088110: Numbers n such that 2^n + n and 2^n - n are both noncomposite

Source: https://oeis.org/A088110

Conjecture (OEIS A088110):
The set of nonnegative integers `n` such that both `2^n + n` and `2^n - n` are noncomposite
(i.e., equal to `1` or prime) is finite.

Conventions:
- Offset: `1`; known terms: `0, 1, 3, 9`.
- Since `2^n ≥ n + 1` for all `n : ℕ`, both `2^n + n` and `2^n - n` are positive integers,
  and natural-number subtraction `2^n - n` is exact.
-/

namespace OMA.S_oeis_a088110

/-- Predicate stating that a natural number `m` is noncomposite (equal to `1` or prime). -/
def IsNoncomposite (m : ℕ) : Prop :=
  m = 1 ∨ Nat.Prime m

/-- The set of natural numbers `n` such that `2^n + n` and `2^n - n` are noncomposite (OEIS A088110). -/
def S : Set ℕ :=
  {n : ℕ | IsNoncomposite (2 ^ n + n) ∧ IsNoncomposite (2 ^ n - n)}

/-- Conjecture: the set of terms of OEIS A088110 is finite. -/
theorem main : Set.Finite S := by
  sorry

end OMA.S_oeis_a088110
