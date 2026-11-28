import Mathlib

/-!
# Ellipse with Rational Axes and Simple Closed-Form Perimeter

Source: https://math.stackexchange.com/questions/4173323/is-there-an-ellipse-with-rational-major-and-minor-axes-which-has-a-simple-clos
-- Credit: @Dugongue (agent: Claude Code, model claude-opus-5-5)
Draft from an earlier generic agent run; audited against the source and re-checked before submission.

## Problem Statement
Other than a circle (`a = b`) or the degenerate case (`b = 0`), is there an
ellipse with rational semi-major and semi-minor axes `0 < b < a` whose perimeter
`4 * a * ∫_0^(π/2) √(1 - (1 - (b/a)^2) sin^2 θ) dθ`
can be written as an algebraic number, or an algebraic multiple of an algebraic
power of `π` (i.e., `α * π^β` with `α, β` algebraic over `ℚ`)?

## Formalization Notes
We express the perimeter using the interval integral over `0` to `π / 2`.
Note that `α * π^0 = α` and `α * π^1 = α * π` are special cases of `α * π^β`
with `IsAlgebraic ℚ α` and `IsAlgebraic ℚ β`.
-/

namespace OMA.S_mse_4173323

noncomputable def ellipsePerimeter (a b : ℝ) : ℝ :=
  4 * a * ∫ θ in (0 : ℝ)..(Real.pi / 2),
    Real.sqrt (1 - (1 - (b / a) ^ 2) * (Real.sin θ) ^ 2)

theorem main :
    ∃ a b : ℚ, 0 < b ∧ b < a ∧
      ∃ α β : ℝ, IsAlgebraic ℚ α ∧ IsAlgebraic ℚ β ∧
        ellipsePerimeter a b = α * Real.pi ^ β := by
  sorry

end OMA.S_mse_4173323
