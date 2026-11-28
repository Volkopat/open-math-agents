import Mathlib.Data.Nat.Choose.Basic
import Mathlib.Data.Rat.Defs

/-!
# OEIS A005559

R. J. Mathar's conjectured recurrence for a column of Guy's square-lattice walk counts.
The sequence has offset 1. We use Paul D. Hanna's 2004 binomial formula from the same
entry. For `n = j + 2`, all the floor and ceiling indices are natural numbers.
The rational embedding lets the signed polynomial identity use ordinary subtraction.

Source: https://oeis.org/A005559
Credit: @wtho704
-/

namespace OMA.S_oeis_a005559

/-- Hanna's binomial formula, with the first term supplied at the sequence's offset. -/
def a : ℕ → ℚ
  | 0 => 0
  | 1 => 1
  | j + 2 =>
      (((j + 3).choose ((j + 2) / 2) : ℕ) : ℚ) * (j + 2).choose ((j + 1) / 2) -
      (((j + 3).choose ((j + 1) / 2) : ℕ) : ℚ) * (j + 2).choose (j / 2)

/-- All three indices lie in the one-indexed sequence starting at `n = 3`. -/
theorem main : ∀ n : ℕ, 3 ≤ n →
    -((n : ℚ) - 1) * (2 * n + 1) * (n + 4) * (n + 3) * a n +
    4 * (n + 1) * (2 * (n : ℚ) ^ 2 + 4 * n + 9) * a (n - 1) +
    16 * n * ((n : ℚ) - 1) * (2 * n + 3) * (n + 1) * a (n - 2) = 0 := by
  sorry

end OMA.S_oeis_a005559
