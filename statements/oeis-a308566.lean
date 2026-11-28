import Mathlib

/-!
# A308566: n = w^2 + x(x+1) + 4^y * 5^z

Source: https://oeis.org/A308566

A308566 (offset 1): `a(n)` is the number of ways to write `n` as `w^2 + x*(x+1) + 4^y*5^z` with
`w, x, y, z` nonnegative integers: 1, 1, 1, 2, 3, 2, 4, 3, 1, 3, …  For example
`1 = 0^2 + 0*1 + 4^0*5^0`.

Conjecture (Zhi-Wei Sun, Jun 07 2019): `a(n) > 0` for all `n > 0`. Equivalently, each
`n = 1, 2, 3, …` can be written as `a*(a+1)/2 + b*(b+1)/2 + 4^c*5^d` with `a, b, c, d`
nonnegative integers. The entry notes that `a(n) > 0` for `0 < n < 10^10` (Giovanni Resta).

Since `a(n)` counts the quadruples `(w, x, y, z)` of nonnegative integers with
`w^2 + x*(x+1) + 4^y*5^z = n`, `a(n) > 0` says exactly that such a quadruple exists, and the
conjecture is stated in that form (the form of the sequence definition; the entry's equivalent
form with two triangular numbers rests on Euler's observation quoted there and is not used).

Conventions: `w, x, y, z` range over `ℕ`; the exponents may be `0`.
-/

namespace OMA.S_oeis_a308566

theorem main :
    ∀ n : ℕ, 0 < n → ∃ w x y z : ℕ, w ^ 2 + x * (x + 1) + 4 ^ y * 5 ^ z = n := by
  sorry

end OMA.S_oeis_a308566
