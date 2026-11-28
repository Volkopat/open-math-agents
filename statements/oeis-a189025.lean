import Mathlib.Data.Nat.Prime.Basic
import Mathlib.Analysis.Real.Sqrt

/-!
# A189025: Prime counts in a short interval

Source: https://oeis.org/A189025
Credit: @MMexicann
-/

namespace OMA.S_oeis_a189025

/-- Among positive indices, only the first has no prime in the interval
with lower endpoint excluded and upper endpoint included. -/
theorem main : ∀ n : ℕ, 0 < n →
    ((¬ ∃ p : ℕ, p.Prime ∧ (n : ℝ) - 2 * Real.sqrt (n : ℝ) < (p : ℝ) ∧ p ≤ n) ↔
      n = 1) := by
  sorry

end OMA.S_oeis_a189025
