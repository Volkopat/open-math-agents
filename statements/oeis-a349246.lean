import Mathlib

/-!
# A349246: n = w^8 + x^4 + 2y^4 + 4z^4 + t(t+1)

Source: https://oeis.org/A349246

A349246 (offset 0): `a(n)` is the number of ways to write `n` as
`w^8 + x^4 + 2*y^4 + 4*z^4 + t*(t+1)`, where `w, x, y, z` and `t` are nonnegative integers:
1, 2, 3, 4, 4, 4, 5, 6, 5, 4, …  For example `145 = 0^8 + 3^4 + 2*0^4 + 4*2^4 + 0*1`.

Conjecture (Zhi-Wei Sun, Mar 26 2022): `a(n) > 0` for all `n = 0, 1, 2, …`. The entry notes that
this has been verified for all `n = 0..10^8`.

Since `a(n)` counts the quintuples `(w, x, y, z, t)` of nonnegative integers with
`w^8 + x^4 + 2*y^4 + 4*z^4 + t*(t+1) = n`, `a(n) > 0` says exactly that such a quintuple exists,
and the conjecture is stated in that form.

Conventions: everything is in `ℕ`.
-/

namespace OMA.S_oeis_a349246

theorem main :
    ∀ n : ℕ, ∃ w x y z t : ℕ, w ^ 8 + x ^ 4 + 2 * y ^ 4 + 4 * z ^ 4 + t * (t + 1) = n := by
  sorry

end OMA.S_oeis_a349246
