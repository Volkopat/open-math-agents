import Mathlib

/-!
# A294074: a primality criterion for p*2^k + 1 with p an odd prime and k odd

Source: https://oeis.org/A294074

A294074 (offset 1): the primes of the form `p*2^k + 1`, where `p` is an odd prime and `k` is
odd: 7, 11, 23, 41, 47, 59, 83, 89, 97, 107, …

Conjecture (Arkadiusz Wesolowski, Feb 07 2018): a number of the form `p*2^k + 1` (with odd
prime `p` and odd `k`) belongs to this sequence if and only if `p*2^k + 1` divides
`(p + 2)^(p*2^k) - 1`. The entry notes that this has been verified for `n` up to `10^10`.

A number `p*2^k + 1` of the stated form belongs to the sequence exactly when it is prime, so
the conjecture is stated as: for every odd prime `p` and every odd `k`, `p*2^k + 1` is prime if
and only if it divides `(p + 2)^(p*2^k) - 1`.

Conventions: an odd prime is a prime different from 2; everything is in `ℕ`, and the
subtraction of 1 is exact.
-/

namespace OMA.S_oeis_a294074

theorem main :
    ∀ p k : ℕ, Nat.Prime p → p ≠ 2 → Odd k →
      (Nat.Prime (p * 2 ^ k + 1) ↔ p * 2 ^ k + 1 ∣ (p + 2) ^ (p * 2 ^ k) - 1) := by
  sorry

end OMA.S_oeis_a294074
