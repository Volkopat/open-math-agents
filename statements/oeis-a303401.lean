import Mathlib

/-!
# A303401: sums of two pentagonal numbers and two powers of 3

Source: https://oeis.org/A303401

A303401 (offset 1): `a(n)` is the number of ways to write `n` as
`a*(3*a-1)/2 + b*(3*b-1)/2 + 3^c + 3^d` with `a, b, c, d` nonnegative integers:
0, 1, 1, 2, 1, 2, 2, 2, 1, 2, 2, 4, …

Conjecture (Zhi-Wei Sun, Apr 23 2018): `a(n) > 0` for all `n > 1`. In other words, any integer
`n > 1` can be written as the sum of two pentagonal numbers and two powers of 3. The entry notes
that `a(n) > 0` for all `n = 2..7*10^6`.

The conjecture is stated in the entry's own in-other-words form: existence of `a, b, c, d`.

Conventions:
- The pentagonal numbers are `a*(3*a-1)/2` with `a ≥ 0` (0, 1, 5, 12, 22, …), as in the sequence
  definition. In `ℕ` the truncated subtraction `3*a - 1` only matters at `a = 0`, where the
  product is `0` anyway, and the division by 2 is exact because `a*(3a-1)` is even.
- The exponents may be `0`, so `1 = 3^0` is an allowed power of 3.
-/

namespace OMA.S_oeis_a303401

theorem main :
    ∀ n : ℕ, 1 < n →
      ∃ a b c d : ℕ, a * (3 * a - 1) / 2 + b * (3 * b - 1) / 2 + 3 ^ c + 3 ^ d = n := by
  sorry

end OMA.S_oeis_a303401
