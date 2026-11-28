import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Order.Lattice.Nat

namespace OMA.S_oeis_a175406

/-- `a(n)` (OEIS A175406): the greatest natural number `k` such that `(1 + 1 / n)^k ≤ 2`. -/
noncomputable def a (n : ℕ) : ℕ :=
  sSup {k : ℕ | (1 + (1 : ℝ) / (n : ℝ)) ^ k ≤ 2}

/-- Conjecture by Charles R Greathouse IV (OEIS A175406): for all `n ≥ 1`,
`a(n) = ⌊(n + 1 / 2) * log 2⌋`. (Disproved; first fails at `n = 1121626023352383`.) -/
theorem main : ∀ n : ℕ, 1 ≤ n → a n = Nat.floor (((n : ℝ) + 1 / 2) * Real.log 2) := by
  sorry

end OMA.S_oeis_a175406
