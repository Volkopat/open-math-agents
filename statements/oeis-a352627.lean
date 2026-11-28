import Mathlib

/-!
# A352627: n = a^2 + 2b^2 + c^4 + 4d^4 + c^2 d^2

Source: https://oeis.org/A352627

A352627 (offset 0): `a(n)` is the number of ways to write `n` as
`a^2 + 2*b^2 + c^4 + 4*d^4 + c^2*d^2`, where `a, b, c, d` are nonnegative integers:
1, 2, 2, 2, 3, 2, 3, 3, 3, 4, 4, 1, …  For example `11 = 3^2 + 2*1^2 + 0^4 + 4*0^4 + 0^2*0^2`.

Conjecture (Zhi-Wei Sun, Mar 24 2022): `a(n) > 0` for all `n = 0, 1, 2, …`. In other words, each
nonnegative integer can be written as `a^2 + 2*b^2 + c^4 + 4*d^4 + c^2*d^2` with `a, b, c, d`
integers.

Since `a(n)` counts the quadruples of nonnegative integers with
`a^2 + 2*b^2 + c^4 + 4*d^4 + c^2*d^2 = n`, `a(n) > 0` says exactly that such a quadruple exists,
and the conjecture is stated in that form.

Conventions: `a, b, c, d` range over `ℕ`. Since the form only involves even powers, allowing
all integers (as in the entry's in-other-words sentence) gives the same set of values.
-/

namespace OMA.S_oeis_a352627

theorem main :
    ∀ n : ℕ, ∃ a b c d : ℕ, a ^ 2 + 2 * b ^ 2 + c ^ 4 + 4 * d ^ 4 + c ^ 2 * d ^ 2 = n := by
  sorry

end OMA.S_oeis_a352627
