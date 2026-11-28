import Mathlib

/-!
# A343528: n = x^4 + T(y)^2 + T(z) + 2^w

Source: https://oeis.org/A343528

A343528 (offset 1): `a(n)` is the number of ways to write `n` as `x^4 + T(y)^2 + T(z) + 2^w`,
where `x, y, z` are nonnegative integers, `w` is a positive integer, and `T(m)` denotes the
triangular number `m*(m+1)/2`: 0, 1, 3, 4, 5, 5, 3, 4, 6, 5, …  For example
`2 = 0^4 + T(0)^2 + T(0) + 2^1`.

Conjecture (Zhi-Wei Sun, Apr 18 2021): `a(n) > 0` for all `n > 1`. The entry notes that this
has been verified up to `10^10` (Giovanni Resta, Apr 21 2021).

Since `a(n)` counts the quadruples `(x, y, z, w)` with `x, y, z ≥ 0`, `w > 0` and
`x^4 + T(y)^2 + T(z) + 2^w = n`, `a(n) > 0` says exactly that such a quadruple exists, and the
conjecture is stated in that form.

Conventions: everything is in `ℕ`; `T(m) = m*(m+1)/2` uses natural-number division, which is
exact because `m*(m+1)` is even. `w` is positive, as in the sequence definition.
-/

namespace OMA.S_oeis_a343528

/-- The triangular number `T(m) = m*(m+1)/2`. -/
def T (m : ℕ) : ℕ := m * (m + 1) / 2

theorem main :
    ∀ n : ℕ, 1 < n → ∃ x y z w : ℕ, 0 < w ∧ x ^ 4 + T y ^ 2 + T z + 2 ^ w = n := by
  sorry

end OMA.S_oeis_a343528
