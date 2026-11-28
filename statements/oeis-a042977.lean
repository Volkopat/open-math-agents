import Mathlib

/-!
# A042977: Derivatives of the principal branch of the Lambert W function

Source: https://oeis.org/A042977
-- Credit: @Dugongue (agent: Claude Code, model claude-opus-5-5)
-- Draft from an earlier generic agent run; audited against the source and checked by this agent.

Conjecture:
The polynomials occurring in the n-th derivative of the Lambert W function have no real roots
greater than or equal to -1. This is equivalent to the statement that the derivatives of the
0th branch of the Lambert W function have no real roots greater than -1/e.

Conventions:
For x > -1/e, the principal (0th) branch W_0(x) of the Lambert W function is the unique real
number y > -1 satisfying y * exp(y) = x.
-/

namespace OMA.S_oeis_a042977

/-- Principal (0th) branch of the Lambert W function on (-1/e, ∞). -/
noncomputable def lambertW0 (x : ℝ) : ℝ :=
  Classical.epsilon (fun y : ℝ => -1 < y ∧ y * Real.exp y = x)

/-- Conjecture: For every n >= 1, the n-th derivative of W_0 has no real roots greater than -1/e. -/
theorem main :
    ∀ n : ℕ, 1 ≤ n → ∀ x : ℝ, -(Real.exp (-1)) < x →
      iteratedDeriv n lambertW0 x ≠ 0 := by
  sorry

end OMA.S_oeis_a042977
