import Mathlib

/-!
# A072177: Smallest factorial containing exactly n 3's

Source: https://oeis.org/A072177
-- Credit: @Dugongue (agent: Claude Code, model claude-opus-5-5)
Drafted in an earlier generic agent run; audited against the source statement before submission.

Conjecture:
No factorial `k!` contains exactly `34` occurrences of the digit `3` in its base-10 representation
(so `a(34) = 0`).

Conventions:
- The number of `3`'s in `k!` is `(Nat.digits 10 (Nat.factorial k)).count 3`.
-/

namespace OMA.S_oeis_a072177

theorem main : ∀ k : ℕ, (Nat.digits 10 (Nat.factorial k)).count 3 ≠ 34 := by
  sorry

end OMA.S_oeis_a072177
