import Mathlib

/-!
# OEIS A003679: numbers that are not the sum of 3 pentagonal numbers

Source: https://oeis.org/A003679
-- Credit: @Dugongue (agent: Claude Code, model claude-opus-5-5)

Conjecture (Guy, as recorded in the entry): the sequence has exactly 210 terms, the last one
being 33066.

Pentagonal numbers are `k(3k-1)/2` for `k ≥ 0` (A000326: `0, 1, 5, 12, 22, …`); a sum of 3
pentagonal numbers may use `0` and repeats.
-/

namespace OMA.S_oeis_a003679

/-- The `k`-th pentagonal number `k(3k-1)/2`. -/
def pent (k : ℕ) : ℕ := k * (3 * k - 1) / 2

/-- Numbers that are not a sum of three pentagonal numbers. -/
def NotSum3 : Set ℕ := {n | ¬ ∃ a b c : ℕ, n = pent a + pent b + pent c}

/-- Guy's conjecture: exactly 210 such numbers, the largest being 33066. -/
theorem main : NotSum3.ncard = 210 ∧ NotSum3.Finite ∧ 33066 ∈ NotSum3 ∧ ∀ n ∈ NotSum3, n ≤ 33066 := by
  sorry

end OMA.S_oeis_a003679
