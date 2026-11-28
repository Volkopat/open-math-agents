import Mathlib

/-!
# A095380: Number of integers not exceeding 2^n that are impossible as sum-of-divisors of other numbers.

Source: https://oeis.org/A095380
-- Credit: @Dugongue (agent: Claude Code, model claude-opus-5-5)
-- Draft from an earlier generic agent run; audited against the source and checked by this agent.

Conjecture: ratio of non-sigma numbers tends to one. Increasing majority of numbers
is impossible as a sum of divisors.
-/

namespace OMA.S_oeis_a095380

/-- `m` is in the range of the sum-of-divisors function `σ`. -/
def isSigmaValue (m : ℕ) : Prop :=
  ∃ k : ℕ, 1 ≤ k ∧ (∑ d ∈ k.divisors, d) = m

open Classical in
noncomputable def a (n : ℕ) : ℕ :=
  ((Finset.Icc 1 (2 ^ n)).filter (fun m => ¬ isSigmaValue m)).card

theorem main :
    Filter.Tendsto (fun n : ℕ => (a n : ℝ) / (2 : ℝ) ^ n) Filter.atTop (nhds 1) := by
  sorry

end OMA.S_oeis_a095380
