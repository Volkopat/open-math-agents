import Mathlib

/-!
# OEIS A068129: Infinitely Many Triangular Numbers with Any Triangular Digit Sum

Source: https://oeis.org/A068129
-- Credit: @Dugongue (agent: Claude Code, model claude-opus-5-5)
Drafted in an earlier generic agent run; audited against the source statement before submission.

Conjecture: For every triangular number $T$ (of the form $m(m + 1)/2$ for $m \ge 1$),
there exist infinitely many triangular numbers whose base-10 digit sum equals $T$.
-/

namespace OMA.S_oeis_a068129

/-- `IsTriangular k` holds when `k = m * (m + 1) / 2` for some `m : ℕ`. -/
def IsTriangular (k : ℕ) : Prop :=
  ∃ m : ℕ, k = m * (m + 1) / 2

/-- Base-10 digit sum of a natural number. -/
def digitSum (k : ℕ) : ℕ :=
  (Nat.digits 10 k).sum

theorem main :
    ∀ T : ℕ, 1 ≤ T → IsTriangular T →
      {k : ℕ | IsTriangular k ∧ digitSum k = T}.Infinite := by
  sorry

end OMA.S_oeis_a068129
