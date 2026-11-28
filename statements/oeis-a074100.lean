import Mathlib

/-!
A074100: Cubes using only digits 1, 2, 3, 5 and 7.

Source: https://oeis.org/A074100
-- Credit: @Dugongue (agent: Claude Code, model claude-opus-5-5)
-- Draft from an earlier generic agent run; audited against the source and checked by this agent.

Conjecture: the sequence is finite.
-/

namespace OMA.S_oeis_a074100

/-- Conjecture: there are only finitely many positive cubes whose base-10 digits all lie in {1, 2, 3, 5, 7}. -/
theorem main :
    {k : ℕ | 0 < k ∧ ∀ d ∈ Nat.digits 10 (k ^ 3), d ∈ ({1, 2, 3, 5, 7} : Set ℕ)}.Finite := by sorry

end OMA.S_oeis_a074100
