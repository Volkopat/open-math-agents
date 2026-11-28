import Mathlib

/-!
# A023811: Largest metadrome in base n

Source: https://oeis.org/A023811
-- Credit: @Dugongue (agent: Claude Code, model claude-opus-5-5)
Drafted in an earlier generic agent run; audited against the source statement before submission.

Conjecture (Gerald McGarvey, 2004): Let `a(n)` be the largest metadrome (integer with
strictly ascending digits) in base `n` (`n ≥ 2`), namely
`a(n) = ∑_{k = 1}^{n - 1} k * n^(n - 1 - k)`.
Then `lim_{n → ∞} (a(n) / a(n - 1) - a(n - 1) / a(n - 2)) = exp 1`.
-/

namespace OMA.S_oeis_a023811

open Filter Topology

/-- Largest metadrome in base `n`: digits `1, 2, ..., n - 1` in base `n`. -/
def a (n : ℕ) : ℕ :=
  ∑ k ∈ Finset.Icc 1 (n - 1), k * n ^ (n - 1 - k)

theorem main :
    Tendsto (fun n : ℕ => (a n : ℝ) / (a (n - 1) : ℝ) - (a (n - 1) : ℝ) / (a (n - 2) : ℝ))
      atTop (nhds (Real.exp 1)) := by
  sorry

end OMA.S_oeis_a023811
