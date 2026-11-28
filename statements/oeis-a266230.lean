import Mathlib

/-!
# A266230: every integer m has m + x^2 = y^3 + z^3 with x, y, z positive

Source: https://oeis.org/A266230

A266230 (offset 0): `a(n)` is the least positive integer `x` such that `n + x^2 = y^3 + z^3` for
some positive integers `y` and `z`, or 0 if no such `x` exists: 3, 1, 3703, 5, 43, 2, 119, 3, …
For example `a(0) = 3` since `0 + 3^2 = 1^3 + 2^3`, and `a(2) = 3703` since
`2 + 3703^2 = 107^3 + 232^3`.

Conjecture (Zhi-Wei Sun, Dec 24 2015): for any integer `m`, there are positive integers `x`,
`y` and `z` such that `m + x^2 = y^3 + z^3`. The entry notes that this has been verified for all
integers `m` with `|m| ≤ 25000`.

Conventions: `m` ranges over all integers, including the negative ones, exactly as in the
conjecture (the sequence itself only records `m = n ≥ 0`). `x`, `y`, `z` are positive integers,
and the equation is stated in `ℤ`.
-/

namespace OMA.S_oeis_a266230

theorem main :
    ∀ m : ℤ, ∃ x y z : ℤ, 0 < x ∧ 0 < y ∧ 0 < z ∧ m + x ^ 2 = y ^ 3 + z ^ 3 := by
  sorry

end OMA.S_oeis_a266230
