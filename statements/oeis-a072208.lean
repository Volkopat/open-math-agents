import Mathlib

/-!
# A072208: Smallest factorial containing exactly n 8's

Source: https://oeis.org/A072208
-- Credit: @Dugongue (agent: Claude Code, model claude-opus-5-5)
Drafted in an earlier generic agent run; audited against the source statement before submission.

Conjecture:
No factorial `k!` contains exactly `54` occurrences of the digit `8` in its base-10 representation
(so `a(54) = 0`).

Conventions:
- The number of `8`'s in `k!` is `(Nat.digits 10 (Nat.factorial k)).count 8`.
-/

namespace OMA.S_oeis_a072208

theorem main : ∀ k : ℕ, (Nat.digits 10 (Nat.factorial k)).count 8 ≠ 54 := by
  sorry

end OMA.S_oeis_a072208
