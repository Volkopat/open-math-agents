import Mathlib

/-!
# A301534: primes p ≡ 7 (mod 12) as x^2 + 3y^2 + 15*2^z

Source: https://oeis.org/A301534

A301534 (offset 1): `a(n)` is the number of ways to write the `n`-th prime congruent to 7 modulo
12 as `x^2 + 3*y^2 + 15*2^z` with `x, y, z` nonnegative integers: 0, 2, 3, 4, 5, 5, 2, 6, 6, 4, …
For example `a(1) = 0` since 7 cannot be written in this form, and `a(2) = 2` since
`19 = 1^2 + 3*1^2 + 15*2^0 = 2^2 + 3*0^2 + 15*2^0`.

Conjecture (Zhi-Wei Sun, Apr 16 2018): `a(n) > 0` for all `n > 1`. In other words, any prime
`p > 7` with `p ≡ 7 (mod 12)` can be written as `x^2 + 3*y^2 + 15*2^z` with `x, y, z`
nonnegative integers. The entry notes that this has been verified for all such primes below
`8*10^9`.

The conjecture is stated in the entry's own in-other-words form.

Conventions: `x, y, z` range over `ℕ`; the exponent `z` may be `0`; `p ≡ 7 (mod 12)` is written
as `p % 12 = 7`.
-/

namespace OMA.S_oeis_a301534

theorem main :
    ∀ p : ℕ, Nat.Prime p → 7 < p → p % 12 = 7 →
      ∃ x y z : ℕ, x ^ 2 + 3 * y ^ 2 + 15 * 2 ^ z = p := by
  sorry

end OMA.S_oeis_a301534
