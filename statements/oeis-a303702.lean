import Mathlib

/-!
# A303702: even numbers as a prime plus a power of 2 plus a power of 3

Source: https://oeis.org/A303702

A303702 (offset 1): `a(n)` is the number of ways to write `2*n` as `p + 2^k + 3^m`, where `p` is
a prime, and `k` and `m` are nonnegative integers: 0, 1, 2, 3, 4, 5, 5, 7, 6, 6, …  For example
`a(2) = 1` since `2*2 = 2 + 2^0 + 3^0` with 2 prime.

Conjecture (Zhi-Wei Sun, Apr 29 2018): `a(n) > 0` for all `n > 1`. In other words, any even
number greater than 2 can be written as the sum of a prime, a power of 2 and a power of 3. The
entry notes that `a(n) > 0` for `n ≤ 2*10^12` (Jud McCranie, Aug 17 2023).

Since `a(n)` counts the triples `(p, k, m)` with `p` prime and `p + 2^k + 3^m = 2n`, `a(n) > 0`
says exactly that such a triple exists, and the conjecture is stated in that form.

Conventions: everything is in `ℕ`; the exponents may be `0`, so `1 = 2^0 = 3^0` is allowed, as
in the entry's examples.
-/

namespace OMA.S_oeis_a303702

theorem main :
    ∀ n : ℕ, 1 < n → ∃ p k m : ℕ, Nat.Prime p ∧ p + 2 ^ k + 3 ^ m = 2 * n := by
  sorry

end OMA.S_oeis_a303702
