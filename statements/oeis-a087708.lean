import Mathlib

/-!
# A087708: First integer > n reached under x -> (5/3) * ceiling(x)

Source: https://oeis.org/A087708
-- Credit: @Dugongue (agent: Claude Code, model claude-opus-5-5)
-- Draft from an earlier generic agent run; audited against the source and checked by this agent.

First integer > n reached under iteration of the map x -> (5/3) * ceiling(x)
when started at n (n >= 1), or -1 if no such integer is ever reached.
Conjecture: An integer > n is always reached.
-/

namespace OMA.S_oeis_a087708

/-- The iteration `x ↦ (5/3) * ceiling(x)` starting from `n`. -/
def iter (n : ℕ) : ℕ → ℚ
  | 0 => (n : ℚ)
  | k + 1 => (5 / 3 : ℚ) * (⌈iter n k⌉ : ℚ)

theorem main :
    ∀ n : ℕ, 1 ≤ n → ∃ k : ℕ, (iter n k).den = 1 ∧ (n : ℚ) < iter n k := by
  sorry

end OMA.S_oeis_a087708
