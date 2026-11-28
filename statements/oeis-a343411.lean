import Mathlib

/-!
# A343411: n = x^3 + [y^3/2] + [z^3/3] + 2^w

Source: https://oeis.org/A343411

A343411 (offset 1): `a(n)` is the number of ways to write `n` as
`x^3 + [y^3/2] + [z^3/3] + 2^w`, where `[.]` is the floor function, `x, y, z` are positive
integers, and `w` is a nonnegative integer: 0, 1, 1, 1, 2, 1, 2, 1, 4, 1, …  For example
`2 = 1^3 + [1^3/2] + [1^3/3] + 2^0`.

Conjecture (Zhi-Wei Sun, Apr 14 2021): `a(n) > 0` for all `n > 1`. The entry notes that this
has been verified up to `10^10` (Giovanni Resta, Apr 14 2021).

Since `a(n)` counts the quadruples `(x, y, z, w)` with `x, y, z > 0`, `w ≥ 0` and
`x^3 + [y^3/2] + [z^3/3] + 2^w = n`, `a(n) > 0` says exactly that such a quadruple exists, and
the conjecture is stated in that form.

Conventions: everything is in `ℕ`, and the floor `[m/k]` of a nonnegative quotient is the
natural-number division `m / k`. `x, y, z` are positive and `w` is any natural number, as in
the sequence definition.
-/

namespace OMA.S_oeis_a343411

theorem main :
    ∀ n : ℕ, 1 < n →
      ∃ x y z w : ℕ, 0 < x ∧ 0 < y ∧ 0 < z ∧ x ^ 3 + y ^ 3 / 2 + z ^ 3 / 3 + 2 ^ w = n := by
  sorry

end OMA.S_oeis_a343411
