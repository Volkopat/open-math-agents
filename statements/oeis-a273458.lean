import Mathlib

/-!
# A273458: n = x^2 + y^2 + z^2 + w^2 with x - y + z + w a nonnegative cube

Source: https://oeis.org/A273458

A273458 (offset 0): `a(n)` is the number of ordered ways to write `n` as `x^2 + y^2 + z^2 + w^2`
with `x - y + z + w` a nonnegative cube, where `x, y, z, w` are integers with `x ≥ y ≥ 0` and
`x ≥ |z| ≤ |w|`: 1, 2, 2, 3, 2, 2, 3, 3, 2, 2, 3, 2, 1, …  For example `a(12) = 1` since
`12 = 3^2 + 1^2 + (-1)^2 + (-1)^2` with `3 - 1 + (-1) + (-1) = 0^3`.

Conjecture (Zhi-Wei Sun, May 22 2016): `a(n) > 0` for all `n = 0, 1, 2, …`.

Since `a(n)` counts the quadruples `(x, y, z, w)` of integers satisfying the stated conditions,
`a(n) > 0` says exactly that such a quadruple exists, and the conjecture is stated in that form.

Conventions:
- `x, y, z, w` range over `ℤ`, and `n` over `ℕ` (cast to `ℤ` in the equation).
- The chained condition `x ≥ |z| ≤ |w|` means `|z| ≤ x` and `|z| ≤ |w|`.
- A nonnegative cube is `m^3` with `m` a nonnegative integer; it is written with `m : ℕ`.
-/

namespace OMA.S_oeis_a273458

theorem main :
    ∀ n : ℕ, ∃ x y z w : ℤ, x ^ 2 + y ^ 2 + z ^ 2 + w ^ 2 = (n : ℤ) ∧ 0 ≤ y ∧ y ≤ x ∧
      |z| ≤ x ∧ |z| ≤ |w| ∧ ∃ m : ℕ, x - y + z + w = (m : ℤ) ^ 3 := by
  sorry

end OMA.S_oeis_a273458
