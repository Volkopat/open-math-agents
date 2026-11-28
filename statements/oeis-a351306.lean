import Mathlib

/-!
# A351306: n = u^4 + v^4 - (x^4 + y^4) with rational u, v, x, y and x^4 + y^4 ≤ n^2

Source: https://oeis.org/A351306

A351306 (offset 0): `a(n)` is the least positive integer `m` such that
`m^4*n = u^4 + v^4 - (x^4 + y^4)` for some nonnegative integers `u, v, x, y` with
`x^4 + y^4 ≤ m^4*n^2`: 1, 1, 1, 10, 2, 2, 2, 4, 6, 4, …  For example `a(3) = 10` with
`10^4*3 = 8^4 + 13^4 - (4^4 + 7^4)` and `4^4 + 7^4 ≤ 10^4*3^2`.

Conjecture (Zhi-Wei Sun, Feb 06 2022): each `n ≥ 0` can be written as
`u^4 + v^4 - (x^4 + y^4)`, where `u, v, x, y` are rational numbers with `x^4 + y^4 ≤ n^2`. In
other words, `a(n)` exists for any nonnegative integer `n`. (The entry recalls a result of
R. Norrie: any rational number is `u^4 + v^4 - (x^4 + y^4)` with `u, v, x, y` rational.)

The conjecture is stated in its first form, with rational `u, v, x, y`. (Dividing the defining
equation of `a(n)` by `m^4` shows that this is the same as the existence of `a(n)`.)

Conventions: `u, v, x, y` range over `ℚ`, and `n` over `ℕ` (cast to `ℚ`).
-/

namespace OMA.S_oeis_a351306

theorem main :
    ∀ n : ℕ, ∃ u v x y : ℚ, (n : ℚ) = u ^ 4 + v ^ 4 - (x ^ 4 + y ^ 4) ∧
      x ^ 4 + y ^ 4 ≤ (n : ℚ) ^ 2 := by
  sorry

end OMA.S_oeis_a351306
