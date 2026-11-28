import Mathlib

/-!
# A308584: n = a(a+1)/2 + b(b+1)/2 + 5^c * 8^d

Source: https://oeis.org/A308584

A308584 (offset 1): `a(n)` is the number of ways to write `n` as
`a*(a+1)/2 + b*(b+1)/2 + 5^c*8^d`, where `a, b, c, d` are nonnegative integers with `a ≤ b`:
1, 1, 1, 1, 2, 1, 3, 3, 2, 2, …  For example `13 = 3*4/2 + 3*4/2 + 5^0*8^0`.

Conjecture (Zhi-Wei Sun, Jun 08 2019): `a(n) > 0` for all `n > 0`. Equivalently, each
`n = 1, 2, 3, …` can be written as `w^2 + x*(x+1) + 5^y*8^z` with `w, x, y, z` nonnegative
integers. The entry notes that `a(n) > 0` for all `0 < n < 10^10` (Giovanni Resta).

Since `a(n)` counts the quadruples `(a, b, c, d)` of nonnegative integers with `a ≤ b` and
`a*(a+1)/2 + b*(b+1)/2 + 5^c*8^d = n`, `a(n) > 0` says exactly that such a quadruple exists, and
the conjecture is stated in that form (the form of the sequence definition). The ordering
condition `a ≤ b` only removes double counting and does not affect existence, so it is omitted.

Conventions: `a, b, c, d` range over `ℕ`; the triangular number `a*(a+1)/2` uses natural-number
division, which is exact; the exponents may be `0`.
-/

namespace OMA.S_oeis_a308584

theorem main :
    ∀ n : ℕ, 0 < n →
      ∃ a b c d : ℕ, a * (a + 1) / 2 + b * (b + 1) / 2 + 5 ^ c * 8 ^ d = n := by
  sorry

end OMA.S_oeis_a308584
