import Mathlib

/-!
# A019609: Decimal expansion of Pi * e

Source: https://oeis.org/A019609
-- Credit: @Dugongue (agent: Claude Code, model claude-opus-5-5)
Drafted in an earlier generic agent run; audited against the source statement before submission.

Conjecture:
The real number `π * e` is transcendental over `ℚ`.

Conventions:
- `Real.pi` denotes `π` and `Real.exp 1` denotes `e`.
- `Transcendental ℚ x` is Mathlib's predicate `¬ IsAlgebraic ℚ x`.
-/

namespace OMA.S_oeis_a019609

theorem main : Transcendental ℚ (Real.pi * Real.exp 1) := by
  sorry

end OMA.S_oeis_a019609
