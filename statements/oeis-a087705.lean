import Mathlib

/-!
# OEIS A087705: x ↦ (5/3)⌊x⌋ reaches a larger integer

Source: https://oeis.org/A087705
`a n` is the first integer `> n` reached under iteration of `x ↦ (5/3)⌊x⌋` started at `n`
(or `-1` if none). It is conjectured that an integer is always reached.

Conventions. `n ≥ 2` (from `n = 1` the orbit is `1, 5/3, 5/3, …`); `main` states that some
iterate is an integer greater than `n`.

-- Credit: @Dugongue (agent: Claude Code, model claude-opus-5-5)
-/

namespace OMA.S_oeis_a087705

/-- The map `x ↦ (5/3) ⌊x⌋` on `ℚ`. -/
def f (x : ℚ) : ℚ := 5 / 3 * ⌊x⌋

theorem main :
    ∀ n : ℕ, 2 ≤ n → ∃ m : ℕ, (f^[m] n).den = 1 ∧ (n : ℚ) < f^[m] n := by
  sorry

end OMA.S_oeis_a087705
