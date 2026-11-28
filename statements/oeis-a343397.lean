import Mathlib

/-!
# A343397: n = 2^x + [y^2/3] + [z^2/4]

Source: https://oeis.org/A343397

A343397 (offset 1): `a(n)` is the number of ways to write `n` as `2^x + [y^2/3] + [z^2/4]` with
`x, y, z` positive integers, where `[.]` is the floor function: 0, 1, 2, 3, 4, 4, 5, 5, 8, 5, …
For example `2 = 2^1 + [1^2/3] + [1^2/4]`.

Conjecture (Zhi-Wei Sun, Apr 13 2021): `a(n) > 0` for all `n > 1`. The entry notes that this
has been verified up to `10^10` (Giovanni Resta, Apr 14 2021).

Since `a(n)` counts the triples `(x, y, z)` of positive integers with
`2^x + [y^2/3] + [z^2/4] = n`, `a(n) > 0` says exactly that such a triple exists, and the
conjecture is stated in that form.

Conventions: everything is in `ℕ`, and the floor `[m/k]` of a nonnegative quotient is the
natural-number division `m / k`. `x, y, z` are positive, as in the sequence definition.
-/

namespace OMA.S_oeis_a343397

theorem main :
    ∀ n : ℕ, 1 < n →
      ∃ x y z : ℕ, 0 < x ∧ 0 < y ∧ 0 < z ∧ 2 ^ x + y ^ 2 / 3 + z ^ 2 / 4 = n := by
  sorry

end OMA.S_oeis_a343397
