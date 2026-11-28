import Mathlib

/-!
# OEIS A066812: Numbers k with phi(k + 1) = phi(k - 1)

Source: https://oeis.org/A066812
-- Credit: @Dugongue (agent: Claude Code, model claude-opus-5-5)
-- Draft from an earlier generic agent run; audited against the source and checked by this agent.

Let $a(1) < a(2) < \cdots$ be the increasing sequence of integers $k \ge 1$ such that
$\phi(k + 1) = \phi(k - 1)$.

Conjecture: The sequence is infinite and there exists a constant $c$ with $2 < c < 2.1$
such that $a(n) \sim n^c$ as $n \to \infty$, i.e., $a(n) / n^c \to 1$.
-/

namespace OMA.S_oeis_a066812

/-- `IsPhiEqualNeighbor k` holds when `k ≥ 1` and `φ(k + 1) = φ(k - 1)`. -/
def IsPhiEqualNeighbor (k : ℕ) : Prop :=
  1 ≤ k ∧ Nat.totient (k + 1) = Nat.totient (k - 1)

theorem main :
    {k : ℕ | IsPhiEqualNeighbor k}.Infinite ∧
      ∃ c : ℝ, (2 : ℝ) < c ∧ c < (21 : ℝ) / 10 ∧
        Filter.Tendsto
          (fun n : ℕ => (Nat.nth IsPhiEqualNeighbor n : ℝ) / ((n + 1 : ℝ) ^ c))
          Filter.atTop (nhds 1) := by
  sorry

end OMA.S_oeis_a066812
