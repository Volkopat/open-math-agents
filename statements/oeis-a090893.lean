import Mathlib

/-!
# OEIS A090893: solutions of a floor equation with r = √3

Source: https://oeis.org/A090893
`a n` lists the solutions `x` of `⌊x r ⌊x / r⌋⌋ = ⌊(x / r) ⌊x r⌋⌋` with `r = √3`. It seems that
`a(n) = 3n + o(n)`; conjecture: `a(n) = 3n + O(1)`.

Conventions. Solutions are natural numbers `x`, listed in increasing order from `a 0`
(offset `0`); `O(1)` means `|a(n) - 3n| ≤ C` for a constant `C`.

-- Credit: @Dugongue (agent: Claude Code, model claude-opus-5-5)
-/

namespace OMA.S_oeis_a090893

open Real

/-- `x` solves the floor equation with `r = √3`. -/
def P (x : ℕ) : Prop :=
  ⌊(x : ℝ) * √3 * ⌊(x : ℝ) / √3⌋⌋ = ⌊(x : ℝ) / √3 * ⌊(x : ℝ) * √3⌋⌋

theorem main : ∃ C : ℝ, ∀ n : ℕ, |(Nat.nth P n : ℝ) - 3 * n| ≤ C := by
  sorry

end OMA.S_oeis_a090893
