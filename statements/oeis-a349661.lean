import Mathlib

/-!
# A349661: n = x^4 + y^2 + (z^2 + 4^w)/2

Source: https://oeis.org/A349661

A349661 (offset 1): `a(n)` is the number of ways to write `n` as `x^4 + y^2 + (z^2 + 4^w)/2`
with `x, y, z, w` nonnegative integers: 1, 3, 3, 2, 4, 5, 2, 2, 4, 5, …  For example
`1 = 0^4 + 0^2 + (1^2 + 4^0)/2` and `23 = 1^4 + 3^2 + (5^2 + 4^0)/2`.

Conjecture (Zhi-Wei Sun, Dec 08 2021): `a(n) > 0` for all `n > 0`. The entry notes that this
has been verified for `n` up to `10^6`, and that it gives a refinement of Lagrange's four-square
theorem.

Since `a(n)` counts the quadruples `(x, y, z, w)` of nonnegative integers with
`x^4 + y^2 + (z^2 + 4^w)/2 = n`, `a(n) > 0` says exactly that such a quadruple exists, and the
conjecture is stated in that form.

Conventions: everything is in `ℕ`. The quotient `(z^2 + 4^w)/2` is the exact rational quotient
and `n` is an integer, so `z^2 + 4^w` must be even; to avoid division the equation is multiplied
by 2: `2*x^4 + 2*y^2 + z^2 + 4^w = 2*n`.
-/

namespace OMA.S_oeis_a349661

theorem main :
    ∀ n : ℕ, 0 < n →
      ∃ x y z w : ℕ, 2 * x ^ 4 + 2 * y ^ 2 + z ^ 2 + 4 ^ w = 2 * n := by
  sorry

end OMA.S_oeis_a349661
