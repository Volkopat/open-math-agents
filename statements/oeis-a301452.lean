import Mathlib

/-!
# A301452: the 2-3 conjecture, n^2 = m*4^k + x^2 + 2y^2 with m in {2, 3}

Source: https://oeis.org/A301452

A301452 (offset 1): `a(n)` is the number of ways to write `n^2` as `m*4^k + x^2 + 2*y^2` with `m`
in the set `{2, 3}` and `k, x, y` nonnegative integers: 0, 2, 2, 2, 2, 5, 3, 2, 4, 4, …  For
example `a(2) = 2` since `2^2 = 2*4^0 + 0^2 + 2*1^2` and `2^2 = 3*4^0 + 1^2 + 2*0^2`.

Conjecture (Zhi-Wei Sun, Mar 21 2018, called the 2-3 conjecture in the entry): `a(n) > 0` for
all `n > 1`. The entry notes that this has been verified for all `n = 2..5*10^7`.

Since `a(n)` counts the quadruples `(m, k, x, y)` with `m ∈ {2, 3}`, `k, x, y` nonnegative
integers and `m*4^k + x^2 + 2*y^2 = n^2`, `a(n) > 0` says exactly that such a quadruple exists,
and the conjecture is stated in that form.

Conventions: everything is in `ℕ`; the exponent `k` may be `0`.
-/

namespace OMA.S_oeis_a301452

theorem main :
    ∀ n : ℕ, 1 < n →
      ∃ m k x y : ℕ, (m = 2 ∨ m = 3) ∧ m * 4 ^ k + x ^ 2 + 2 * y ^ 2 = n ^ 2 := by
  sorry

end OMA.S_oeis_a301452
