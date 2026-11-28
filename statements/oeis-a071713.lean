import Mathlib

/-!
# A071713: Conjectured minimum 12 for |x^5 + y^5 + z^5| with distinct nonzero integers

Source: https://oeis.org/A071713
-- Credit: @Dugongue (agent: Claude Code, model claude-opus-5-5)
Drafted in an earlier generic agent run; audited against the source statement before submission.

Title: A071713: a(n) = smallest value of |x^n + y^n + z^n| for x, y, z distinct nonzero integers.

Statement:
The conjectured minimum of 12 for a(5) can be achieved by (x, y, z) = (13, 16, -17).
-/

namespace OMA.S_oeis_a071713

theorem main :
    ∀ x y z : ℤ,
      x ≠ 0 → y ≠ 0 → z ≠ 0 →
      x ≠ y → y ≠ z → x ≠ z →
      12 ≤ |x ^ 5 + y ^ 5 + z ^ 5| := by
  sorry

end OMA.S_oeis_a071713
