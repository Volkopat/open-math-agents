import Mathlib

/-!
# A033286: a(n) = n * prime(n).

Source: https://oeis.org/A033286
Credit: @luciusacarr

The entry's comments record one conjecture.

Conjecture (Zhi-Wei Sun, Oct 08 2025). Any integer n >= 3070 can be written as a weighted sum of
four primes, where each prime p is assigned the weight pi(p) (the index of p). In other words,
every n = 3070, 3071, ... is a sum of four terms of the current sequence. (Verified for
n <= 2*10^5.)

Reading of the source:
* The index of a prime `p` is `pi(p) = Nat.primeCounting p` (so `pi(2) = 1`, `pi(3) = 2`, ...),
  and the term of the sequence with index `m` is `m * prime(m) = pi(p) * p` for `p = prime(m)`.
* The four primes need not be distinct (a "sum of four terms" allows repeated terms).
* `n` ranges over the natural numbers `n ≥ 3070`.
-/

namespace OMA.S_oeis_a033286

theorem main :
    ∀ n : ℕ, 3070 ≤ n →
      ∃ p q r s : ℕ, p.Prime ∧ q.Prime ∧ r.Prime ∧ s.Prime ∧
        n = Nat.primeCounting p * p + Nat.primeCounting q * q +
          Nat.primeCounting r * r + Nat.primeCounting s * s := by
  sorry

end OMA.S_oeis_a033286
