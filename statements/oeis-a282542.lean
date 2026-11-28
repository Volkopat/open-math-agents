import Mathlib

/-!
# A282542: n = x^2 + y^2 + z^2 + w^2 with x + 3y + 5z and one of y, z, w squares

Source: https://oeis.org/A282542

A282542 (offset 0): `a(n)` is the number of ways to write `n` as `x^2 + y^2 + z^2 + w^2` with
`x, y, z, w` nonnegative integers such that `x + 3*y + 5*z` and (at least) one of `y, z, w` are
squares: 1, 2, 2, 2, 2, 1, 1, 1, 1, 3, 3, 2, 1, …  For example `a(12) = 1` since
`12 = 1^2 + 1^2 + 1^2 + 3^2` with `1 + 3*1 + 5*1 = 3^2` and `1 = 1^2`.

Conjecture (Zhi-Wei Sun, Feb 17 2017): `a(n) > 0` for all `n = 0, 1, 2, …`. The entry notes
that this is stronger than the 1-3-5 conjecture (cf. A271518).

Since `a(n)` counts the quadruples `(x, y, z, w)` of nonnegative integers satisfying the stated
conditions, `a(n) > 0` says exactly that such a quadruple exists, and the conjecture is stated
in that form.

Conventions: `x, y, z, w` range over `ℕ`, and a square is a perfect square `j^2` with `j ≥ 0`
(`IsSquare` in `ℕ`), so `0` counts as a square, as in the entry's examples.
-/

namespace OMA.S_oeis_a282542

theorem main :
    ∀ n : ℕ, ∃ x y z w : ℕ, x ^ 2 + y ^ 2 + z ^ 2 + w ^ 2 = n ∧ IsSquare (x + 3 * y + 5 * z) ∧
      (IsSquare y ∨ IsSquare z ∨ IsSquare w) := by
  sorry

end OMA.S_oeis_a282542
