import Mathlib

/-!
# A102341: Areas of 'close-to-equilateral' integer triangles.

Source: https://oeis.org/A102341
-- Credit: @Dugongue (agent: Claude Code, model claude-opus-5-5)
Drafted in an earlier generic agent run; audited against the source statement before submission.

Weak conjecture: There are only finitely many nondegenerate 'close-to-equilateral' integer
triangles (triangles with integer sides `1 <= a <= b <= c`, `c = a + 1`, and positive
integer area).
-/

namespace OMA.S_oeis_a102341

/-- Predicate for a nondegenerate close-to-equilateral Heronian triangle with integer sides
`1 ≤ a ≤ b ≤ c`, `c = a + 1`, and positive integer area. -/
def IsCloseToEquilateralHeronian (t : ℕ × ℕ × ℕ) : Prop :=
  let (a, b, c) := t
  1 ≤ a ∧ a ≤ b ∧ b ≤ c ∧ c = a + 1 ∧
  ∃ A : ℕ, 1 ≤ A ∧
    16 * A ^ 2 = (a + b + c) * (a + b - c) * (a + c - b) * (b + c - a)

theorem main :
    {t : ℕ × ℕ × ℕ | IsCloseToEquilateralHeronian t}.Finite := by
  sorry

end OMA.S_oeis_a102341
