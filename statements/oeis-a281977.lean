import Mathlib

/-!
# A281977: n = x^2 + y^2 + z^2 + w^2 with x and -7x - 8y + 8z + 16w both squares

Source: https://oeis.org/A281977

A281977 (offset 0): `a(n)` is the number of ways to write `n` as `x^2 + y^2 + z^2 + w^2` with
`x, y, z, w` nonnegative integers such that both `x` and `-7*x - 8*y + 8*z + 16*w` are squares:
1, 1, 3, 2, 2, 3, 2, 2, 2, 2, 2, 3, 1, …  For example `a(12) = 1` since
`12 = 1^2 + 1^2 + 3^2 + 1^2` with `1 = 1^2` and `-7*1 - 8*1 + 8*3 + 16*1 = 5^2`.

Conjecture (Zhi-Wei Sun, Feb 04 2017): `a(n) > 0` for all `n = 0, 1, 2, …`. The entry notes
that this has been verified for `n` up to `10^8` (Qing-Hu Hou).

Since `a(n)` counts the quadruples `(x, y, z, w)` of nonnegative integers satisfying the stated
conditions, `a(n) > 0` says exactly that such a quadruple exists, and the conjecture is stated
in that form.

Conventions:
- `x, y, z, w` range over `ℕ`. The linear form `-7x - 8y + 8z + 16w` can be negative, so it is
  evaluated in `ℤ`.
- A square is the square of an integer; `IsSquare` in `ℤ` (which forces the value to be
  nonnegative) and `IsSquare` in `ℕ` for `x`. Zero counts as a square, as in the entry's
  examples.
-/

namespace OMA.S_oeis_a281977

theorem main :
    ∀ n : ℕ, ∃ x y z w : ℕ, x ^ 2 + y ^ 2 + z ^ 2 + w ^ 2 = n ∧ IsSquare x ∧
      IsSquare (-7 * (x : ℤ) - 8 * (y : ℤ) + 8 * (z : ℤ) + 16 * (w : ℤ)) := by
  sorry

end OMA.S_oeis_a281977
