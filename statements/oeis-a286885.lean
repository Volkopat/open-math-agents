import Mathlib

/-!
# A286885: 6n + 1 = x^2 + 3y^2 + 54z^2

Source: https://oeis.org/A286885

A286885 (offset 0): `a(n)` is the number of ways to write `6n + 1` as `x^2 + 3y^2 + 54z^2` with
`x, y, z` nonnegative integers: 1, 1, 1, 1, 1, 1, 1, 1, 2, 1, 2, 2, …

Conjecture (Zhi-Wei Sun, Aug 02 2017): `a(n) > 0` for all `n = 0, 1, 2, …`.

Since `a(n)` counts the triples `(x, y, z)` of nonnegative integers with
`x^2 + 3y^2 + 54z^2 = 6n + 1`, `a(n) > 0` says exactly that such a triple exists, and the
conjecture is stated in that form.

Conventions: `x, y, z` range over `ℕ` (nonnegative integers, as in the entry), and `n` ranges
over all of `ℕ`, including `n = 0` (where `1 = 1^2 + 3*0^2 + 54*0^2`).
-/

namespace OMA.S_oeis_a286885

theorem main :
    ∀ n : ℕ, ∃ x y z : ℕ, x ^ 2 + 3 * y ^ 2 + 54 * z ^ 2 = 6 * n + 1 := by
  sorry

end OMA.S_oeis_a286885
