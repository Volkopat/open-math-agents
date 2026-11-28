import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Topology.Algebra.InfiniteSum.Basic

/-!
# A016744: Reciprocal sums for the fourth powers of even integers

Source: https://oeis.org/A016744
Credit: @MMexicann
-/

namespace OMA.S_oeis_a016744

/-- Both sums range over the positive indices of the sequence `(2n)^4`.
The summands use `n + 1` to enumerate those indices starting from zero. -/
theorem main :
    HasSum (fun n : ℕ ↦ (1 : ℝ) / (2 * ((n : ℝ) + 1)) ^ 4) (Real.pi ^ 4 / 1440) ∧
      HasSum (fun n : ℕ ↦ (-1 : ℝ) ^ (n + 2) / (2 * ((n : ℝ) + 1)) ^ 4)
        (7 * Real.pi ^ 4 / 11520) := by
  sorry

end OMA.S_oeis_a016744
