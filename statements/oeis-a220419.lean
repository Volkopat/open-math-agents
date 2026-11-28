import Mathlib

/-!
# A220419: n = x + y with 2x + 1, 2y - 1 and x^3 + 2y^3 all prime

Source: https://oeis.org/A220419

A220419 (offset 1): `a(n)` is the number of ways to write `n = x + y` (`x > 0`, `y > 0`) with
`2x + 1`, `2y - 1` and `x^3 + 2y^3` all prime. For example `a(25) = 1` since `25 = 3 + 22` with
`7`, `43` and `3^3 + 2*22^3 = 21323` all prime.

Conjecture (Zhi-Wei Sun, Dec 14 2012): `a(n) > 0` for all `n > 527`. The entry notes that this
has been verified for `n` up to `2*10^7` and that it implies the Goldbach conjecture, since
`2(x + y) = (2x + 1) + (2y - 1)`.

Since `a(n)` counts the pairs `(x, y)` of positive integers with `x + y = n` and `2x + 1`,
`2y - 1`, `x^3 + 2y^3` all prime, `a(n) > 0` says exactly that such a pair exists, and the
conjecture is stated in that form. The seven similar conjectures (1)-(7) listed afterwards in
the entry are separate claims and are not part of this statement.

Conventions: everything is in `ℕ`; `2*y - 1` is an exact subtraction because `y > 0`. The bound
`527` is sharp in the sense that `a(527) = 0`.
-/

namespace OMA.S_oeis_a220419

theorem main :
    ∀ n : ℕ, 527 < n →
      ∃ x y : ℕ, 0 < x ∧ 0 < y ∧ x + y = n ∧ Nat.Prime (2 * x + 1) ∧ Nat.Prime (2 * y - 1) ∧
        Nat.Prime (x ^ 3 + 2 * y ^ 3) := by
  sorry

end OMA.S_oeis_a220419
