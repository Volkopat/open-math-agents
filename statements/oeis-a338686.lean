import Mathlib

/-!
# A338686: n = x^5 + y^2 + [z^2/7]

Source: https://oeis.org/A338686

A338686 (offset 1): `a(n)` is the number of ways to write `n` as `x^5 + y^2 + [z^2/7]`, where
`x, y, z` are integers with `x ≥ 0`, `y ≥ 1` and `z ≥ 2`, and `[.]` is the floor function:
1, 2, 2, 3, 3, 3, 3, 2, 3, 4, …  For example `1 = 0^5 + 1^2 + [2^2/7]` and
`166 = 0^5 + 1^2 + [34^2/7]`.

Conjecture (Zhi-Wei Sun, Apr 23 2021): `a(n) > 0` for all `n > 0`. The entry notes that this
has been verified up to `2*10^9` (Giovanni Resta, Apr 28 2021).

Since `a(n)` counts the triples `(x, y, z)` with `x ≥ 0`, `y ≥ 1`, `z ≥ 2` and
`x^5 + y^2 + [z^2/7] = n`, `a(n) > 0` says exactly that such a triple exists, and the conjecture
is stated in that form.

Conventions: everything is in `ℕ`, and the floor `[m/k]` of a nonnegative quotient is the
natural-number division `m / k`. The lower bounds `y ≥ 1` and `z ≥ 2` are those of the sequence
definition.
-/

namespace OMA.S_oeis_a338686

theorem main :
    ∀ n : ℕ, 0 < n → ∃ x y z : ℕ, 1 ≤ y ∧ 2 ≤ z ∧ x ^ 5 + y ^ 2 + z ^ 2 / 7 = n := by
  sorry

end OMA.S_oeis_a338686
