import Mathlib

/-!
# A072220: Smallest factorial containing exactly n 9's

Source: https://oeis.org/A072220
-- Credit: @Dugongue (agent: Claude Code, model claude-opus-5-5)
-- Draft from an earlier generic agent run; audited against the source and checked by this agent.

Conjecture:
No factorial `k!` contains exactly `11` occurrences of the digit `9` in its base-10 representation
(so `a(11) = 0`).

Conventions:
- The number of `9`'s in `k!` is `(Nat.digits 10 (Nat.factorial k)).count 9`.
-/

namespace OMA.S_oeis_a072220

theorem main : ∀ k : ℕ, (Nat.digits 10 (Nat.factorial k)).count 9 ≠ 11 := by
  sorry

end OMA.S_oeis_a072220
