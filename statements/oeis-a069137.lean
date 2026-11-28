import Mathlib

/-!
# A069137: Numbers that are not the sum of 6 nonnegative cubes

Source: https://oeis.org/A069137

Conjecture (OEIS A069137):
The set of nonnegative integers that cannot be written as the sum of 6 nonnegative cubes
(equivalently, sums of neither 1, 2, 3, 4, 5, nor 6 nonnegative cubes) is finite.

Conventions:
- Offset: `1`; first terms: `7, 14, 15, 21, 22, 23, 42, 47, 49, 50, 61, 77, ...`.
- Allowing `0^3` makes "sum of at most 6 nonnegative cubes" identical to "sum of 6 nonnegative cubes".
-/

namespace OMA.S_oeis_a069137

/-- Predicate stating that `n` can be expressed as a sum of 6 cubes of natural numbers. -/
def IsSumOfSixCubes (n : ℕ) : Prop :=
  ∃ a b c d e f : ℕ, n = a ^ 3 + b ^ 3 + c ^ 3 + d ^ 3 + e ^ 3 + f ^ 3

/-- The set of natural numbers that are not a sum of 6 nonnegative cubes (OEIS A069137). -/
def S : Set ℕ :=
  {n : ℕ | ¬ IsSumOfSixCubes n}

/-- Conjecture: there are only finitely many natural numbers that are not a sum of 6 nonnegative cubes. -/
theorem main : Set.Finite S := by
  sorry

end OMA.S_oeis_a069137
