import Mathlib

/-!
# A303429: n - 3^k - 5^m as a sum of two squares

Source: https://oeis.org/A303429

A303429 (offset 1): `a(n)` is the number of ordered pairs `(k, m)` of nonnegative integers such
that `n - 3^k - 5^m` can be written as the sum of two squares: 0, 1, 1, 2, 1, 3, 2, 3, 2, 4, …
For example `a(5) = 1` with `5 - 3^1 - 5^0 = 0^2 + 1^2`.

Conjecture (Zhi-Wei Sun, Apr 28 2018): `a(n) > 0` for all `n > 1`. The entry notes that this is
equivalent to the author's conjecture in A303656 and that it has been verified for all
`n = 2..10^9`.

`a(n) > 0` says exactly that some pair `(k, m)` makes `n - 3^k - 5^m` a sum of two squares of
integers, i.e. that `n = 3^k + 5^m + x^2 + y^2` for some nonnegative integers `k, m, x, y`, and
the conjecture is stated in that form.

Conventions: everything is in `ℕ`; the equation is written additively so that no subtraction is
needed (a sum of two integer squares is nonnegative, and the squares may be taken with
nonnegative bases). `0^2` is allowed, as in the entry's example.
-/

namespace OMA.S_oeis_a303429

theorem main :
    ∀ n : ℕ, 1 < n → ∃ k m x y : ℕ, 3 ^ k + 5 ^ m + x ^ 2 + y ^ 2 = n := by
  sorry

end OMA.S_oeis_a303429
