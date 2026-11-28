import Mathlib

/-!
# A275656: n = 4^k*(1 + x^2 + y^2) + z^2 with x ≤ y ≤ z

Source: https://oeis.org/A275656

A275656 (offset 1): `a(n)` is the number of ordered ways to write `n` as
`4^k*(1 + x^2 + y^2) + z^2`, where `k, x, y, z` are nonnegative integers with `x ≤ y ≤ z`:
1, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 3, …  For example `a(22) = 1` since
`22 = 4^0*(1 + 1^2 + 2^2) + 4^2` with `1 < 2 < 4`.

Conjecture (Zhi-Wei Sun, Aug 04 2016): `a(n) > 0` for all `n > 0`. The entry notes
that this is stronger than Lagrange's four-square theorem.

Since `a(n)` counts the quadruples `(k, x, y, z)` of nonnegative integers with `x ≤ y ≤ z` and
`4^k*(1 + x^2 + y^2) + z^2 = n`, `a(n) > 0` says exactly that such a quadruple exists, and the
conjecture is stated in that form.

Conventions: `k, x, y, z` range over `ℕ`. The ordering `x ≤ y ≤ z` is part of the statement: the
variable `z` does not play the same role as `x` and `y`, so the condition `y ≤ z` is a genuine
restriction and is kept.
-/

namespace OMA.S_oeis_a275656

theorem main :
    ∀ n : ℕ, 0 < n →
      ∃ k x y z : ℕ, x ≤ y ∧ y ≤ z ∧ 4 ^ k * (1 + x ^ 2 + y ^ 2) + z ^ 2 = n := by
  sorry

end OMA.S_oeis_a275656
