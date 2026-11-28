import Mathlib

/-!
# A300752: n = x^2 + y^2 + z^2 + w^2 with x + 3y + 5z a positive square and 3x, y or z a square

Source: https://oeis.org/A300752

A300752 (offset 1): `a(n)` is the number of ways to write `n` as `x^2 + y^2 + z^2 + w^2` with
`x + 3*y + 5*z` a positive square, where `x, y, z, w` are nonnegative integers such that `3*x` or
`y` or `z` is a square: 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, …  For example `a(71) = 1` since
`71 = 3^2 + 1^2 + 6^2 + 5^2` with `1 = 1^2` and `3 + 3*1 + 5*6 = 6^2`.

Conjecture (Zhi-Wei Sun, Mar 11 2018): `a(n) > 0` for all `n = 1, 2, 3, …`. The entry notes that
this is stronger than the author's 1-3-5 conjecture in A271518, and that it has been verified
for `n` up to `1.05*10^11` (A. Machiavelo, R. Reis and N. Tsopanidis, 2020).

Since `a(n)` counts the quadruples `(x, y, z, w)` of nonnegative integers satisfying the stated
conditions, `a(n) > 0` says exactly that such a quadruple exists, and the conjecture is stated
in that form.

Conventions: `x, y, z, w` range over `ℕ`, and a square is a perfect square `j^2` with `j ≥ 0`
(`IsSquare` in `ℕ`), so `0` counts as a square in the last condition, as in the entry's
examples. A positive square is a square that is positive.
-/

namespace OMA.S_oeis_a300752

theorem main :
    ∀ n : ℕ, 0 < n →
      ∃ x y z w : ℕ, x ^ 2 + y ^ 2 + z ^ 2 + w ^ 2 = n ∧ 0 < x + 3 * y + 5 * z ∧
        IsSquare (x + 3 * y + 5 * z) ∧ (IsSquare (3 * x) ∨ IsSquare y ∨ IsSquare z) := by
  sorry

end OMA.S_oeis_a300752
