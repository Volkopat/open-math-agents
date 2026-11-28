import Mathlib

/-!
# A087704: Steps for x -> (5/3) * floor(x) to reach an integer > n

Source: https://oeis.org/A087704
-- Credit: @Dugongue (agent: Claude Code, model claude-opus-5-5)
Drafted in an earlier generic agent run; audited against the source statement before submission.

Number of steps for iteration of the map x -> (5/3) * floor(x) to reach an
integer > n when started at n (n >= 2), or -1 if no such integer is ever reached.
Conjecture: An integer > n is always reached.
-/

namespace OMA.S_oeis_a087704

/-- The iteration `x ↦ (5/3) * floor(x)` starting from `n`. -/
def iter (n : ℕ) : ℕ → ℚ
  | 0 => (n : ℚ)
  | k + 1 => (5 / 3 : ℚ) * (⌊iter n k⌋ : ℚ)

theorem main :
    ∀ n : ℕ, 2 ≤ n → ∃ k : ℕ, (iter n k).den = 1 ∧ (n : ℚ) < iter n k := by
  sorry

end OMA.S_oeis_a087704
