import Mathlib

/-!
# A079411: a(1)=1, a(n) = n - a(a(ceiling(n/2)))

Source: https://oeis.org/A079411
-- Credit: @Dugongue (agent: Claude Code, model claude-opus-5-5)
-- Draft from an earlier generic agent run; audited against the source and checked by this agent.

a(1) = 1, a(n) = n - a(a(ceiling(n/2))).
a(n) is asymptotic to n*(sqrt(3)-1); conjecture: (a(n) - n*(sqrt(3)-1))/log(n) is bounded.
-/

namespace OMA.S_oeis_a079411

def IsA079411 (a : ℕ → ℕ) : Prop :=
  a 1 = 1 ∧ ∀ n : ℕ, 2 ≤ n → a n = n - a (a ((n + 1) / 2))

theorem main :
    ∀ a : ℕ → ℕ, IsA079411 a →
      ∃ C : ℝ, ∀ n : ℕ, 2 ≤ n →
        |((a n : ℝ) - (n : ℝ) * (Real.sqrt 3 - 1)) / Real.log (n : ℝ)| ≤ C := by
  sorry

end OMA.S_oeis_a079411
