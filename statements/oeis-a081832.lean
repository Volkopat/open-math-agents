import Mathlib

/-!
# A081832: a(1)=a(2)=1, a(n) = a(n+1-2*a(n-1)) + a(n-2*a(n-2))

Source: https://oeis.org/A081832
-- Credit: @Dugongue (agent: Claude Code, model claude-opus-5-5)
Drafted in an earlier generic agent run; audited against the source statement before submission.

a(1) = a(2) = 1, a(n) = a(n + 1 - 2*a(n-1)) + a(n - 2*a(n-2)).
Conjectures: a(n)/n -> 1/4, and a(n+1) - a(n) is 0 or 1 for all n >= 1.
-/

namespace OMA.S_oeis_a081832

def IsA081832 (a : ℕ → ℕ) : Prop :=
  a 1 = 1 ∧ a 2 = 1 ∧
  ∀ n : ℕ, 3 ≤ n → a n = a (n + 1 - 2 * a (n - 1)) + a (n - 2 * a (n - 2))

theorem main :
    ∀ a : ℕ → ℕ, IsA081832 a →
      Filter.Tendsto (fun n : ℕ => (a n : ℝ) / (n : ℝ)) Filter.atTop (nhds (1 / 4 : ℝ)) ∧
      ∀ n : ℕ, 1 ≤ n → a (n + 1) = a n ∨ a (n + 1) = a n + 1 := by
  sorry

end OMA.S_oeis_a081832
