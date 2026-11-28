import Mathlib

/-!
# A087665: First integer reached by b(0) = n/4, b(k) = b(k-1) * floor(b(k-1))

Source: https://oeis.org/A087665
-- Credit: @Dugongue (agent: Claude Code, model claude-opus-5-5)
-- Draft from an earlier generic agent run; audited against the source and checked by this agent.

Consider the recurrence b(0) = n/4, b(k) = b(k-1) * floor(b(k-1)). The sequence
gives the first integer reached, or -1 if no integer is ever reached.
Conjecture: An integer is always reached if the initial value n/4 is >= 2 (i.e. n >= 8).
-/

namespace OMA.S_oeis_a087665

/-- The rational recurrence `b(0) = n/4`, `b(k+1) = b(k) * floor(b(k))`. -/
def b (n : ℕ) : ℕ → ℚ
  | 0 => (n : ℚ) / 4
  | k + 1 => b n k * (⌊b n k⌋ : ℚ)

theorem main :
    ∀ n : ℕ, 8 ≤ n → ∃ k : ℕ, (b n k).den = 1 := by
  sorry

end OMA.S_oeis_a087665
