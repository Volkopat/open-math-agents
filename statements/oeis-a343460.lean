import Mathlib

/-!
# A343460: n = x^6 + y^3 + z(3z+1)/2 + 2^k

Source: https://oeis.org/A343460

A343460 (offset 1): `a(n)` is the number of ways to write `n` as
`x^6 + y^3 + z*(3*z+1)/2 + 2^k`, where `x` and `y` are nonnegative integers, `z` is an integer
and `k` is a positive integer: 0, 1, 3, 5, 6, 5, 4, 4, 6, 9, …  For example
`2 = 0^6 + 0^3 + 0*(3*0+1)/2 + 2^1`, and
`175 = 1^6 + 3^3 + (-10)*(3*(-10)+1)/2 + 2^1`.

Conjecture (Zhi-Wei Sun, Apr 16 2021): `a(n) > 0` for all `n > 1`. The entry notes that this
has been verified up to `10^10` (Giovanni Resta, Apr 18 2021).

Since `a(n)` counts the quadruples `(x, y, z, k)` with `x, y ≥ 0`, `z` an integer, `k > 0` and
`x^6 + y^3 + z*(3*z+1)/2 + 2^k = n`, `a(n) > 0` says exactly that such a quadruple exists, and
the conjecture is stated in that form.

Conventions:
- `x, y, k` range over `ℕ` (with `k > 0`) and `z` over `ℤ`, as in the sequence definition; the
  equation is stated in `ℤ`.
- `z*(3*z+1)/2` uses integer division by 2, which is exact because `z*(3z+1)` is even for every
  integer `z`.
-/

namespace OMA.S_oeis_a343460

theorem main :
    ∀ n : ℕ, 1 < n →
      ∃ x y k : ℕ, ∃ z : ℤ, 0 < k ∧
        (x : ℤ) ^ 6 + (y : ℤ) ^ 3 + z * (3 * z + 1) / 2 + 2 ^ k = (n : ℤ) := by
  sorry

end OMA.S_oeis_a343460
