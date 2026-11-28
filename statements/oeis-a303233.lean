import Mathlib

/-!
# A303233: sums of two triangular numbers and two powers of 2

Source: https://oeis.org/A303233

A303233 (offset 1): `a(n)` is the number of ways to write `n` as
`a*(a+1)/2 + b*(b+1)/2 + 2^c + 2^d`, where `a, b, c, d` are nonnegative integers with `a ≤ b`
and `c ≤ d`: 0, 1, 2, 3, 4, 5, 4, 6, 7, 7, …

Conjecture (Zhi-Wei Sun, Apr 20 2018): `a(n) > 0` for all `n > 1`. In other words, any integer
`n > 1` can be written as the sum of two triangular numbers and two powers of 2. The entry notes
that `a(n) > 0` for all `n = 2..10^9`.

The conjecture is stated in the entry's own in-other-words form. The ordering conditions `a ≤ b`
and `c ≤ d` only remove double counting and do not affect existence, so they are omitted.

Conventions: `a, b, c, d` range over `ℕ`; the triangular number `a*(a+1)/2` uses natural-number
division, which is exact because `a*(a+1)` is even. The exponents may be `0`, so `1 = 2^0` is an
allowed power of 2 (as in the entry's example `2 = 0 + 0 + 2^0 + 2^0`).
-/

namespace OMA.S_oeis_a303233

theorem main :
    ∀ n : ℕ, 1 < n →
      ∃ a b c d : ℕ, a * (a + 1) / 2 + b * (b + 1) / 2 + 2 ^ c + 2 ^ d = n := by
  sorry

end OMA.S_oeis_a303233
