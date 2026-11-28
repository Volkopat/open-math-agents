import Mathlib

/-!
# OEIS A073226: transcendence of `e^e`

Source: https://oeis.org/A073226
-- Credit: @Dugongue (agent: Claude Code, model claude-opus-5-5)

A073226 is the decimal expansion of `e^e`. The entry notes that a weak form of Schanuel's
conjecture implies that `e^e` is transcendental (Marques–Sondow 2012); `main` states that `e^e`
is transcendental.
-/

namespace OMA.S_oeis_a073226

/-- `e^e` is transcendental. -/
theorem main : Transcendental ℚ (Real.exp (Real.exp 1)) := by
  sorry

end OMA.S_oeis_a073226
