import Mathlib.NumberTheory.SmoothNumbers
import Mathlib.Topology.Instances.Real.Lemmas

/-!
# Exceptional gaps between 5-smooth integers

Source: https://mathoverflow.net/questions/468790
Credit: @MMexicann
-/

namespace OMA.S_mo_468790

/-- The union of intervals between consecutive 5-smooth integers with odd lower endpoint.
Mathlib's smooth-number bound is strict, so the bound 6 includes the prime 5. -/
def exceptional : Set ℕ :=
  {n | ∃ lo hi : ℕ, lo ∈ Nat.smoothNumbers 6 ∧ hi ∈ Nat.smoothNumbers 6 ∧
    Odd lo ∧ n ∈ Set.Ico lo hi ∧
    ∀ m ∈ Nat.smoothNumbers 6, m ∉ Set.Ioo lo hi}

/-- The proportion of integers in the range `[0, N)` in the exceptional intervals. -/
noncomputable def exceptionalProportion (N : ℕ) : ℝ := by
  classical
  exact (((Finset.range N).filter (· ∈ exceptional)).card : ℝ) / N

theorem main : Filter.Tendsto exceptionalProportion Filter.atTop (nhds 0) := by
  sorry

end OMA.S_mo_468790
