import Mathlib

/-!
# A308028: the 2-4-6 conjecture on sums of three odd primes

Source: https://oeis.org/A308028

A308028 (offset 1): `a(n)` is the number of ways to write `2*n+1` as `p + q + r` with
`2*p + 4*q + 6*r` a square, where `p, q, r` are odd primes: 0, 0, 0, 1, 0, 0, 2, 1, 1, 3, …  For
example `a(8) = 1` with `17 = 7 + 5 + 5` and `2*7 + 4*5 + 6*5 = 8^2`.

Conjecture (Zhi-Wei Sun, May 09 2019, called the 2-4-6 conjecture in the entry): `a(n) > 0` for
all `n > 6`. In other words, any odd integer greater than 14 can be written as the sum of three
odd primes `p, q, r` for which `2*p + 4*q + 6*r` is an integer square. The entry notes that this
is stronger than the weak Goldbach conjecture and that it has been verified for all
`n = 7..3*10^5`.

Since `a(n)` counts the triples of odd primes `(p, q, r)` with `p + q + r = 2n + 1` and
`2p + 4q + 6r` a square, `a(n) > 0` says exactly that such a triple exists, and the conjecture is
stated in that form.

Conventions: an odd prime is a prime different from 2; a square is a perfect square (`IsSquare`
in `ℕ`). The three primes play different roles in `2p + 4q + 6r`, so no ordering is imposed.
-/

namespace OMA.S_oeis_a308028

theorem main :
    ∀ n : ℕ, 6 < n →
      ∃ p q r : ℕ, Nat.Prime p ∧ p ≠ 2 ∧ Nat.Prime q ∧ q ≠ 2 ∧ Nat.Prime r ∧ r ≠ 2 ∧
        p + q + r = 2 * n + 1 ∧ IsSquare (2 * p + 4 * q + 6 * r) := by
  sorry

end OMA.S_oeis_a308028
