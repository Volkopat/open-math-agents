import Mathlib

/-!
# A077625: Largest term in periodic part of continued fraction expansion of square root of -1+2^n or 0 if -1+2^n is square.

Source: https://oeis.org/A077625
-- Credit: @Dugongue (agent: Claude Code, model claude-opus-5-5)
Drafted in an earlier generic agent run; audited against the source statement before submission.

a(n) = 0 iff n = 1, as a consequence of Catalan's conjecture or Mihăilescu's theorem.
-/

namespace OMA.S_oeis_a077625

theorem main :
    ∀ n : ℕ, 1 ≤ n → (IsSquare (2 ^ n - 1) ↔ n = 1) := by sorry

end OMA.S_oeis_a077625
