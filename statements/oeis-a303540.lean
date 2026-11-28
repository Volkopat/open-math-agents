import Mathlib

/-!
# A303540: sums of two squares and two central binomial coefficients

Source: https://oeis.org/A303540

A303540 (offset 1): `a(n)` is the number of ways to write `n` as
`a^2 + b^2 + binomial(2*c,c) + binomial(2*d,d)`, where `a, b, c, d` are nonnegative integers with
`a ≤ b` and `c ≤ d`: 0, 1, 2, 3, 2, 2, 3, 4, 3, 2, …  For example
`2 = 0^2 + 0^2 + binomial(0,0) + binomial(0,0)`.

Conjecture (Zhi-Wei Sun, Apr 25 2018): `a(n) > 0` for all `n > 1`. In other words, any integer
`n > 1` can be written as the sum of two squares and two central binomial coefficients. The
entry notes that this has been verified for all `1 < n ≤ 10^11` (Jiao-Min Lin).

The conjecture is stated in the entry's own in-other-words form. The ordering conditions `a ≤ b`
and `c ≤ d` only remove double counting and do not affect existence, so they are omitted.

Conventions: `a, b, c, d` range over `ℕ`; the central binomial coefficient `binomial(2c, c)` is
`(2 * c).choose c`, with `binomial(0, 0) = 1` allowed, as in the entry's example.
-/

namespace OMA.S_oeis_a303540

theorem main :
    ∀ n : ℕ, 1 < n →
      ∃ a b c d : ℕ, a ^ 2 + b ^ 2 + (2 * c).choose c + (2 * d).choose d = n := by
  sorry

end OMA.S_oeis_a303540
