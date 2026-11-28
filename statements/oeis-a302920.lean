import Mathlib

/-!
# A302920: p^2 = x^2 + 2y^2 + 3*2^z for every prime p

Source: https://oeis.org/A302920

A302920 (offset 1): `a(n)` is the number of ways to write `prime(n)^2` as `x^2 + 2*y^2 + 3*2^z`
with `x, y, z` nonnegative integers: 1, 2, 3, 3, 4, 5, 4, 4, 3, 7, …  For example
`prime(1)^2 = 4 = 1^2 + 2*0^2 + 3*2^0`.

Conjecture (Zhi-Wei Sun, Apr 15 2018): `a(n) > 0` for all `n > 0`. In other words, for any prime
`p` there are nonnegative integers `x`, `y` and `z` such that `x^2 + 2*y^2 + 3*2^z = p^2`. (The
entry notes that the analogous statement fails for the composite number
`m = 5884015571 = 7*17*49445509`.)

The conjecture is stated in the entry's own in-other-words form.

Conventions: `x, y, z` range over `ℕ`; the exponent `z` may be `0`.
-/

namespace OMA.S_oeis_a302920

theorem main :
    ∀ p : ℕ, Nat.Prime p → ∃ x y z : ℕ, x ^ 2 + 2 * y ^ 2 + 3 * 2 ^ z = p ^ 2 := by
  sorry

end OMA.S_oeis_a302920
