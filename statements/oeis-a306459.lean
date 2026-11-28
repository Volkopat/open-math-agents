import Mathlib

/-!
# A306459: n as a cube plus three tetrahedral numbers

Source: https://oeis.org/A306459

A306459 (offset 0): `a(n)` is the number of ways to write `n` as
`w^3 + C(x+2,3) + C(y+2,3) + C(z+2,3)`, where `w, x, y, z` are nonnegative integers with
`x ≤ y ≤ z`, and `C(m,k)` denotes the binomial coefficient: 1, 2, 2, 2, 2, 2, 2, 1, 2, 3, …
For example `17 = 2^3 + C(3,3) + C(4,3) + C(4,3)`.

Conjecture (Zhi-Wei Sun, Feb 20 2019): `a(n) > 0` for all `n ≥ 0`. In other words, each
nonnegative integer can be written as the sum of a nonnegative cube and three tetrahedral
numbers. The entry notes that this has been verified for all `n = 0..2*10^6`.

The conjecture is stated in the entry's own in-other-words form. The ordering condition
`x ≤ y ≤ z` only removes double counting among the three tetrahedral numbers and does not affect
existence, so it is omitted.

Conventions: `w, x, y, z` range over `ℕ`, and the tetrahedral numbers are `C(x+2, 3)` =
`(x + 2).choose 3` (0, 1, 4, 10, 20, … for `x = 0, 1, 2, …`).
-/

namespace OMA.S_oeis_a306459

theorem main :
    ∀ n : ℕ, ∃ w x y z : ℕ,
      w ^ 3 + (x + 2).choose 3 + (y + 2).choose 3 + (z + 2).choose 3 = n := by
  sorry

end OMA.S_oeis_a306459
