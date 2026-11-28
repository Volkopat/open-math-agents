import Mathlib

/-!
# A306790: n = x(3x+1)/2 + y(y+1)(y+2)/2 + z(z+1)(z+2)/6 with x nonzero

Source: https://oeis.org/A306790

A306790 (offset 1): `a(n)` is the number of ways to write `n` as
`x*(3*x+1)/2 + y*(y+1)*(y+2)/2 + z*(z+1)*(z+2)/6`, where `x` is a nonzero integer, and `y` and
`z` are nonnegative integers: 1, 2, 1, 1, 4, 3, 1, 3, 3, 1, …  For example `a(59) = 1` with
`59 = (-3)*(3*(-3)+1)/2 + 2*3*4/2 + 5*6*7/6`.

Conjecture (Zhi-Wei Sun, Mar 10 2019): `a(n) > 0` for all `n > 0`. In other words, each positive
integer `n` can be written as the sum of a positive generalized pentagonal number, a tetrahedral
number and a tetrahedral number times three. The entry notes that this has been verified for all
`n = 1..2*10^7`.

Since `a(n)` counts the triples `(x, y, z)` with `x` a nonzero integer, `y, z` nonnegative
integers and `x*(3*x+1)/2 + y*(y+1)*(y+2)/2 + z*(z+1)*(z+2)/6 = n`, `a(n) > 0` says exactly that
such a triple exists, and the conjecture is stated in that form.

Conventions:
- `x` ranges over the nonzero integers and `y`, `z` over `ℕ`, as in the sequence definition; the
  equation is stated in `ℤ`.
- The divisions are integer divisions and are exact: `x*(3x+1)` is even, `y*(y+1)*(y+2)` is
  divisible by 2, and `z*(z+1)*(z+2)` is divisible by 6.
-/

namespace OMA.S_oeis_a306790

theorem main :
    ∀ n : ℕ, 0 < n →
      ∃ x : ℤ, ∃ y z : ℕ, x ≠ 0 ∧
        x * (3 * x + 1) / 2 + ((y : ℤ) * (y + 1) * (y + 2)) / 2 +
          ((z : ℤ) * (z + 1) * (z + 2)) / 6 = (n : ℤ) := by
  sorry

end OMA.S_oeis_a306790
