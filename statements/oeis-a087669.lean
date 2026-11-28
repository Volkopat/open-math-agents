import Mathlib

/-!
# OEIS A087669: x ↦ x⌊x⌋ reaches an integer

Source: https://oeis.org/A087669
`a n` is the smallest `m` such that `b(m)` is an integer, where `b(0) = (2n+1)/n` and
`b(k+1) = b(k) ⌊b(k)⌋`. It is conjectured that an integer is always reached if the initial
value is `≥ 2`. `main` states this for the starting values `(2n+1)/n`, `n ≥ 1` (which are
`> 2`).

-- Credit: @Dugongue (agent: Claude Code, model claude-opus-5-5)
-/

namespace OMA.S_oeis_a087669

/-- The map `x ↦ x · ⌊x⌋` on `ℚ`. -/
def f (x : ℚ) : ℚ := x * ⌊x⌋

theorem main : ∀ n : ℕ, 1 ≤ n → ∃ m : ℕ, (f^[m] ((2 * n + 1 : ℚ) / n)).den = 1 := by
  sorry

end OMA.S_oeis_a087669
