import Mathlib

/-!
# A350021: n = w^4 + x^2 + y^2 + z^2 with x - y a power of two

Source: https://oeis.org/A350021

A350021 (offset 1): `a(n)` is the number of ways to write `n` as `w^4 + x^2 + y^2 + z^2` with
`x - y` a power of two (including `2^0 = 1`): 1, 2, 1, 1, 4, 4, 1, 1, 2, 3, …  For example
`3 = 1^4 + 1^2 + 0^2 + 1^2` with `1 - 0 = 2^0`, and `4 = 0^4 + 2^2 + 0^2 + 0^2` with
`2 - 0 = 2^1`.

Conjecture (Zhi-Wei Sun, Dec 08 2021): `a(n) > 0` for all `n > 0`. The entry notes that this is
a refinement of Lagrange's four-square theorem, verified for `n` up to `10^6`.

Since `a(n)` counts the quadruples `(w, x, y, z)` of nonnegative integers with
`w^4 + x^2 + y^2 + z^2 = n` and `x - y` a power of two, `a(n) > 0` says exactly that such a
quadruple exists, and the conjecture is stated in that form.

Conventions: `w, x, y, z` range over `ℕ` (the listed terms are reproduced with nonnegative
integers). The condition that `x - y` is a power of two is written without subtraction as
`x = y + 2^k` for some `k ≥ 0`.
-/

namespace OMA.S_oeis_a350021

theorem main :
    ∀ n : ℕ, 0 < n →
      ∃ w x y z k : ℕ, x = y + 2 ^ k ∧ w ^ 4 + x ^ 2 + y ^ 2 + z ^ 2 = n := by
  sorry

end OMA.S_oeis_a350021
