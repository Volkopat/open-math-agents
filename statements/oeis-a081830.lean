import Mathlib

/-!
# A081830: Indices k where Hofstadter Q(k) < Q(k+1)

Source: https://oeis.org/A081830
-- Credit: @Dugongue (agent: Claude Code, model claude-opus-5-5)
-- Draft from an earlier generic agent run; audited against the source and checked by this agent.

Numbers k such that the k-th term of Hofstadter Q-sequence is < (k+1)-th term.
Conjecture: a(n)/n -> 2.
-/

namespace OMA.S_oeis_a081830

def IsHofstadterQ (Q : ℕ → ℕ) : Prop :=
  Q 1 = 1 ∧ Q 2 = 1 ∧
  ∀ n : ℕ, 3 ≤ n → Q n = Q (n - Q (n - 1)) + Q (n - Q (n - 2))

theorem main :
    ∀ Q : ℕ → ℕ, IsHofstadterQ Q →
      Filter.Tendsto
        (fun n : ℕ =>
          (Nat.nth (fun k => 1 ≤ k ∧ Q k < Q (k + 1)) n : ℝ) / ((n + 1 : ℕ) : ℝ))
        Filter.atTop (nhds 2) := by
  sorry

end OMA.S_oeis_a081830
