import Mathlib

/-!
# A307981: n = x^3 + 2y^3 + 3z^3 + w(w+1)(w+2)/6

Source: https://oeis.org/A307981

A307981 (offset 0): `a(n)` is the number of ways to write `n` as
`x^3 + 2*y^3 + 3*z^3 + w*(w+1)*(w+2)/6`, where `x, y, z, w` are nonnegative integers:
1, 2, 2, 3, 4, 3, 3, 3, 2, 2, …  For example `19 = 0^3 + 2*2^3 + 3*1^3 + 0*1*2/6`.

Conjecture (Zhi-Wei Sun, May 08 2019): `a(n) > 0` for every nonnegative integer `n`. In other
words, `{x^3 + 2*y^3 + 3*z^3 + w*(w+1)*(w+2)/6 : x, y, z, w = 0, 1, 2, …} = {0, 1, 2, …}`. The
entry notes that this has been verified for all `n = 0..2*10^6`.

The conjecture is stated as: every natural number `n` has such a representation (the reverse
inclusion of the set equality is trivial, since all values are nonnegative integers).

Conventions: `x, y, z, w` range over `ℕ`; the division by 6 is a natural-number division and is
exact, because a product of three consecutive integers is divisible by 6.
-/

namespace OMA.S_oeis_a307981

theorem main :
    ∀ n : ℕ, ∃ x y z w : ℕ,
      x ^ 3 + 2 * y ^ 3 + 3 * z ^ 3 + w * (w + 1) * (w + 2) / 6 = n := by
  sorry

end OMA.S_oeis_a307981
