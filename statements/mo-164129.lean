import Mathlib

/-!
# Improving known bounds for Pierce expansions

Source: https://mathoverflow.net/questions/164129
-- Credit: @Dugongue (agent: Claude Code, model claude-opus-5-5)

For positive integers `a > b` put `b₀ = b` and `bᵢ = a mod bᵢ₋₁`; the sequence strictly
decreases, and `P(a, b)` is the `n` with `bₙ = 0`. Known: `P(a, b) = O(a^(1/3))`, and
`P(a, b) > c log a` for infinitely many `a`. The asker (Shallit) guesses
`P(a, b) = O((log a)²)`; `main` states this guess.

Conventions:
* `O((log a)²)` is uniform in `b`: there is `C` with `P(a, b) ≤ C (log a)²` for all `a > b ≥ 1`
  (then `a ≥ 2`, so `log a > 0`).
-/

namespace OMA.S_mo_164129

/-- Number of steps of `b ↦ a mod b` from `b` down to `0`. -/
def P (a b : ℕ) : ℕ :=
  if h : b = 0 then 0 else 1 + P a (a % b)
termination_by b
decreasing_by exact Nat.mod_lt _ (Nat.pos_of_ne_zero h)

/-- Shallit's guess: `P(a, b) = O((log a)²)`. -/
theorem main : ∃ C : ℝ, ∀ a b : ℕ, 1 ≤ b → b < a → (P a b : ℝ) ≤ C * Real.log a ^ 2 := by
  sorry

end OMA.S_mo_164129
