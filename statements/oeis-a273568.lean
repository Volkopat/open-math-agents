import Mathlib

/-!
# A273568: n = w^2 + x^2 + y^2 + z^2 with w + x + 2y - 4z twice a nonnegative cube

Source: https://oeis.org/A273568

A273568 (offset 0): `a(n)` is the number of ordered ways to write `n` as `w^2 + x^2 + y^2 + z^2`
with `w + x + 2*y - 4*z` twice a nonnegative cube, where `w` is an integer and `x, y, z` are
nonnegative integers: 1, 1, 2, 1, 3, 2, 2, 2, 2, 4, 3, 3, 4, 1, …  For example `a(3) = 1` since
`3 = (-1)^2 + 1^2 + 1^2 + 0^2` with `(-1) + 1 + 2*1 - 4*0 = 2*1^3`.

Conjecture (Zhi-Wei Sun, May 25 2016): `a(n) > 0` for all `n = 0, 1, 2, …`.

Since `a(n)` counts the quadruples `(w, x, y, z)` satisfying the stated conditions, `a(n) > 0`
says exactly that such a quadruple exists, and the conjecture is stated in that form.

Conventions:
- All four variables are taken in `ℤ`; `w` is unrestricted and `x, y, z` are required to be
  nonnegative. `n` ranges over `ℕ` (cast to `ℤ` in the equation).
- Twice a nonnegative cube is `2*m^3` with `m` a nonnegative integer; it is written with
  `m : ℕ`.
-/

namespace OMA.S_oeis_a273568

theorem main :
    ∀ n : ℕ, ∃ w x y z : ℤ, w ^ 2 + x ^ 2 + y ^ 2 + z ^ 2 = (n : ℤ) ∧ 0 ≤ x ∧ 0 ≤ y ∧ 0 ≤ z ∧
      ∃ m : ℕ, w + x + 2 * y - 4 * z = 2 * (m : ℤ) ^ 3 := by
  sorry

end OMA.S_oeis_a273568
