import Mathlib

/-!
# A160326: sums of two squares and a pentagonal number

Source: https://oeis.org/A160326

A160326 (offset 0): `a(n)` is the number of ways to express `n = 0, 1, 2, …` as the sum of two
squares and a pentagonal number, `a(n) = |{(x, y, z) : x, y, z = 0, 1, 2, … and
x^2 + y^2 + (3z^2 - z)/2 = n}|`: 1, 3, 3, 1, 2, 5, 4, 1, 1, 5, 6, 2, …

Conjecture (Zhi-Wei Sun, April 2009, recorded in the entry of May 08 2009): `a(n) > 0` for every
`n = 0, 1, 2, 3, …`.

Since `a(n)` counts the triples `(x, y, z)` with `x^2 + y^2 + (3z^2 - z)/2 = n`, `a(n) > 0` says
exactly that such a triple exists, and the conjecture is stated in that form.

Conventions:
- The pentagonal numbers are the ordinary ones `(3z^2 - z)/2 = z*(3z-1)/2` with `z ≥ 0`
  (0, 1, 5, 12, 22, …), not the generalized pentagonal numbers with `z` any integer: the listed
  terms of A160326 are reproduced only with `z ≥ 0`.
- `x, y, z` range over `ℕ`. In `z * (3 * z - 1) / 2` the truncated subtraction only matters at
  `z = 0`, where the product is `0` anyway, and the division by 2 is exact because `z*(3z-1)` is
  even.
-/

namespace OMA.S_oeis_a160326

theorem main :
    ∀ n : ℕ, ∃ x y z : ℕ, x ^ 2 + y ^ 2 + z * (3 * z - 1) / 2 = n := by
  sorry

end OMA.S_oeis_a160326
