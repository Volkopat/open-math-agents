import Mathlib

/-!
# A073119: Total number of parts which are positive powers of 2 in all partitions of n

Source: https://oeis.org/A073119
-- Credit: @Dugongue (agent: Claude Code, model claude-opus-5-5)
-- Draft from an earlier generic agent run; audited against the source and checked by this agent.

a(n) = total number of parts which are positive powers of 2 (i.e., 2^k with k >= 1)
in all partitions of n.
Conjecture: a(n) ~ exp(sqrt(2*n/3)*Pi) / (2*Pi*sqrt(2*n)) ~ p(n) * sqrt(6*n) / Pi,
where p(n) is the partition function.
-/

namespace OMA.S_oeis_a073119

open Filter Topology
open scoped Classical

/-- Total number of parts of the form `2^k` (`k ≥ 1`) across all partitions of `n`. -/
noncomputable def a (n : ℕ) : ℕ :=
  ∑ P : Nat.Partition n, (P.parts.filter (fun m => ∃ k : ℕ, 1 ≤ k ∧ m = 2 ^ k)).card

theorem main :
    Tendsto
      (fun n : ℕ =>
        (a n : ℝ) /
          (Real.exp (Real.sqrt (2 * (n : ℝ) / 3) * Real.pi) /
            (2 * Real.pi * Real.sqrt (2 * (n : ℝ)))))
      atTop (𝓝 1) ∧
    Tendsto
      (fun n : ℕ =>
        (a n : ℝ) /
          ((Fintype.card (Nat.Partition n) : ℝ) * Real.sqrt (6 * (n : ℝ)) / Real.pi))
      atTop (𝓝 1) := by
  sorry

end OMA.S_oeis_a073119
