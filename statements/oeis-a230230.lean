import Mathlib

/-!
# A230230: 2n = p + q with p, q, 3p - 10, 3q + 10 all prime

Source: https://oeis.org/A230230

A230230 (offset 1): `a(n)` is the number of ways to write `2*n = p + q` with `p`, `q`,
`3*p - 10`, `3*q + 10` all prime. For example `a(5) = 1` since `10 = 7 + 3` with
`3*7 - 10 = 11` and `3*3 + 10 = 19` both prime.

Conjecture (Zhi-Wei Sun, Oct 12 2013): `a(n) > 0` for all `n > 3`. The entry notes that this is
stronger than Goldbach's conjecture for even numbers and that it has been verified for `2*n` up
to `10^9` (Mauro Fiorentini, Jul 08 2023).

Since `a(n)` counts the pairs of primes `(p, q)` with `p + q = 2n` and `3p - 10`, `3q + 10`
prime, `a(n) > 0` says exactly that such a pair exists, and the conjecture is stated in that
form.

Conventions:
- The condition is not symmetric in `p` and `q` and no ordering between them is imposed (the
  listed terms count all such ordered pairs).
- Everything is in `ℕ`. The subtraction `3*p - 10` is truncated only for `p = 2` and `p = 3`,
  where the integer values `-4` and `-1` are not prime and the truncated value `0` is not prime
  either, so the two readings agree.
-/

namespace OMA.S_oeis_a230230

theorem main :
    ∀ n : ℕ, 3 < n →
      ∃ p q : ℕ, p + q = 2 * n ∧ Nat.Prime p ∧ Nat.Prime q ∧ Nat.Prime (3 * p - 10) ∧
        Nat.Prime (3 * q + 10) := by
  sorry

end OMA.S_oeis_a230230
