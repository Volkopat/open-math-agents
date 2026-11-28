import Mathlib

/-!
# A108345: The set N such that each positive integer can be written in the form s^2 + n, s>=0, n in N, in an even number of ways.

Source: https://oeis.org/A108345
-- Credit: @Dugongue (agent: Claude Code, model claude-opus-5-5)
Drafted in an earlier generic agent run; audited against the source statement before submission.

This set is conjectured to have zero density.
-/

namespace OMA.S_oeis_a108345

open Classical in
theorem main :
    ∀ N : Set ℕ, 0 ∈ N →
      (∀ m : ℕ, 1 ≤ m →
        Even ((Finset.range (m + 1)).filter (fun s => s ^ 2 ≤ m ∧ m - s ^ 2 ∈ N)).card) →
      Filter.Tendsto
        (fun M : ℕ => (((Finset.Icc 1 M).filter (fun n => n ∈ N)).card : ℝ) / (M : ℝ))
        Filter.atTop (nhds 0) := by
  sorry

end OMA.S_oeis_a108345
