import Mathlib

/-!
# A302985: n - 2^x - 3*2^y of the form u^2 + 2v^2

Source: https://oeis.org/A302985

A302985 (offset 1): `a(n)` is the number of ordered pairs `(x, y)` of nonnegative integers such
that `n - 2^x - 3*2^y` has the form `u^2 + 2*v^2` with `u` and `v` integers:
0, 0, 0, 1, 2, 2, 4, 5, 4, 5, …  For example `a(4) = 1` with `4 - 2^0 - 3*2^0 = 0^2 + 2*0^2`.

Conjecture (Zhi-Wei Sun, Apr 16 2018): `a(n) > 0` for all `n > 3`. The entry notes that this is
equivalent to the author's conjecture in A302983 and that it has been verified for all
`n = 4..6*10^9`.

`a(n) > 0` says exactly that some pair `(x, y)` makes `n - 2^x - 3*2^y` of the form
`u^2 + 2*v^2`, i.e. that `n = 2^x + 3*2^y + u^2 + 2*v^2` for some nonnegative integers
`x, y, u, v`, and the conjecture is stated in that form.

Conventions: everything is in `ℕ`; the equation is written additively so that no subtraction is
needed (`u^2 + 2*v^2` is nonnegative, and `u`, `v` may be taken nonnegative). The exponents may
be `0`.
-/

namespace OMA.S_oeis_a302985

theorem main :
    ∀ n : ℕ, 3 < n → ∃ x y u v : ℕ, 2 ^ x + 3 * 2 ^ y + u ^ 2 + 2 * v ^ 2 = n := by
  sorry

end OMA.S_oeis_a302985
