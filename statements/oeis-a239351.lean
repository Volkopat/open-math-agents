import Mathlib.Algebra.Order.Ring.Abs

namespace OMA.S_oeis_a239351

/-- An ordered integer triple `(x, y, z)` solving `x^3 + y^3 + z^3 = 3` with
`|x| ≤ |y| ≤ |z|`, as listed in OEIS A239351. -/
def IsA239351Solution (x y z : ℤ) : Prop :=
  x ^ 3 + y ^ 3 + z ^ 3 = 3 ∧ abs x ≤ abs y ∧ abs y ≤ abs z

/-- Conjecture (OEIS A239351): Besides `(1, 1, 1)` and `(4, 4, -5)`, no other integer
solution `(x, y, z)` to `x^3 + y^3 + z^3 = 3` with `|x| ≤ |y| ≤ |z|` exists. -/
theorem main :
    ∀ x y z : ℤ, IsA239351Solution x y z →
      (x = 1 ∧ y = 1 ∧ z = 1) ∨ (x = 4 ∧ y = 4 ∧ z = -5) := by
  sorry

end OMA.S_oeis_a239351
