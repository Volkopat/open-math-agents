import Mathlib

/-!
# A352632: n = (a+b)(a+2b) + c^4 + 2d^4 with a positive

Source: https://oeis.org/A352632

A352632 (offset 1): `a(n)` is the number of ways to write `n` as `(a+b)*(a+2*b) + c^4 + 2*d^4`,
where `a` is a positive integer, and `b, c, d` are nonnegative integers:
1, 1, 1, 2, 1, 2, 2, 1, 2, 1, …  For example `11 = (3+0)*(3+2*0) + 0^4 + 2*1^4` and
`23 = (3+1)*(3+2*1) + 1^4 + 2*1^4`.

Conjecture (Zhi-Wei Sun, Mar 25 2022): `a(n) > 0` for all `n > 0`. In other words, any positive
integer `n` can be written as `u*v + x^4 + 2*y^4`, where `u, v, x, y` are nonnegative integers
with `0 < u ≤ v < 2*u`.

Since `a(n)` counts the quadruples `(a, b, c, d)` with `a > 0`, `b, c, d ≥ 0` and
`(a+b)*(a+2*b) + c^4 + 2*d^4 = n`, `a(n) > 0` says exactly that such a quadruple exists, and the
conjecture is stated in that form (the form of the sequence definition; the substitution
`u = a + b`, `v = a + 2b` gives the entry's in-other-words version).

Conventions: everything is in `ℕ`, with `a` positive.
-/

namespace OMA.S_oeis_a352632

theorem main :
    ∀ n : ℕ, 0 < n →
      ∃ a b c d : ℕ, 0 < a ∧ (a + b) * (a + 2 * b) + c ^ 4 + 2 * d ^ 4 = n := by
  sorry

end OMA.S_oeis_a352632
