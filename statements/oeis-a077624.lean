import Mathlib

/-!
# A077624: Largest term in periodic part of continued fraction expansion of square root of 2^n + 1 or 0 if 2^n + 1 is a square.

Source: https://oeis.org/A077624
-- Credit: @Dugongue (agent: Claude Code, model claude-opus-5-5)
-- Draft from an earlier generic agent run; audited against the source and checked by this agent.

a(n) = 0 iff n = 3, as a consequence of Catalan's conjecture or Mihăilescu's theorem.
-/

namespace OMA.S_oeis_a077624

theorem main :
    ∀ n : ℕ, IsSquare (2 ^ n + 1) ↔ n = 3 := by sorry

end OMA.S_oeis_a077624
