import Mathlib

/-!
# Consecutive members of the sequence of squares and cubes

Source: https://oeis.org/A002760 (OEIS Foundation, CC BY-SA 4.0).
Credit: @connoranderson

A002760 starts with 0 and 1. The comment that names Catalan's conjecture says that
8 and 9 are its only pair of consecutive numbers. We retain the sequence as given.
The customary nontrivial-power version of Catalan's conjecture excludes 0 and 1.
-/

namespace OMA.S_oeis_a002760

/-- Membership in A002760, the union of the natural squares and cubes. -/
def squareOrCube (n : ℕ) : Prop :=
  (∃ a : ℕ, n = a ^ 2) ∨ (∃ a : ℕ, n = a ^ 3)

theorem main : ∀ n : ℕ, (squareOrCube n ∧ squareOrCube (n + 1)) ↔ n = 8 := by
  sorry

end OMA.S_oeis_a002760
