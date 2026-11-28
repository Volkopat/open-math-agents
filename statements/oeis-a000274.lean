import Mathlib.Combinatorics.Derangements.Finite
import Mathlib.Analysis.SpecialFunctions.Exp
import Mathlib.Algebra.Order.Floor.Ring
import Mathlib.Data.Rat.Defs

/-!
# Mathar's factorial-floor formula for A000274

The one-based sequence is given by the derangement formula in the OEIS
entry's Mathematica program. The claimed floor formula is Corollary 3
of Sela Fried's *On sequence A000274 in the OEIS* and holds for `n ≥ 2`.

Sources: https://oeis.org/A000274 and https://oeis.org/A000274/a000274.pdf
Credit: @justusklocke-cloud
-/

namespace OMA.S_oeis_a000274

/-- The one-based value of A000274 from its derangement formula. -/
def a (n : ℕ) : ℚ :=
  ((n - 1 : ℕ) : ℚ) * (numDerangements (n - 1) : ℚ) / 2

theorem main : ∀ n : ℕ, 2 ≤ n →
    a n =
      ((Int.floor ((n.factorial : ℝ) / Real.exp 1) -
        Int.floor (((n - 1).factorial : ℝ) / Real.exp 1) : ℤ) : ℚ) / 2 := by
  sorry

end OMA.S_oeis_a000274
