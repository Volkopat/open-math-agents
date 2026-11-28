import Mathlib

/-!
# A343384: the 3-4-5-6 conjecture, n = [a^3/3] + [b^3/4] + [c^3/5] + [d^6/6]

Source: https://oeis.org/A343384

A343384 (offset 0): `a(n)` is the number of ways to write `n` as
`[a^3/3] + [b^3/4] + [c^3/5] + [d^6/6]` with `a, b, c, d` positive integers, where `[.]` is the
floor function: 1, 1, 2, 2, 1, 2, 1, 3, 1, 3, …  For example
`0 = [1^3/3] + [1^3/4] + [1^3/5] + [1^6/6]` and `1 = [1^3/3] + [1^3/4] + [2^3/5] + [1^6/6]`.

Conjecture (Zhi-Wei Sun, Apr 13 2021, called the 3-4-5-6 conjecture in the entry): `a(n) > 0`
for all `n ≥ 0`. The entry notes that this has been verified up to `2*10^9` (Giovanni Resta,
Apr 28 2021).

Since `a(n)` counts the quadruples `(a, b, c, d)` of positive integers with
`[a^3/3] + [b^3/4] + [c^3/5] + [d^6/6] = n`, `a(n) > 0` says exactly that such a quadruple
exists, and the conjecture is stated in that form.

Conventions: everything is in `ℕ`, and the floor `[m/k]` of a nonnegative quotient is the
natural-number division `m / k`. `a, b, c, d` are positive, as in the sequence definition.
-/

namespace OMA.S_oeis_a343384

theorem main :
    ∀ n : ℕ, ∃ a b c d : ℕ, 0 < a ∧ 0 < b ∧ 0 < c ∧ 0 < d ∧
      a ^ 3 / 3 + b ^ 3 / 4 + c ^ 3 / 5 + d ^ 6 / 6 = n := by
  sorry

end OMA.S_oeis_a343384
