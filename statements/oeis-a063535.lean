import Mathlib

/-!
# A063535: Primes prime(k) such that prime(k+1)^2 < prime(k)*prime(k+2).

Source: https://oeis.org/A063535
Credit: @maaaakks

Conjecture (Clark Kimberling, May 16 2015): "these are the primes such that
prime(k+2) - 2*prime(k+1) + prime(k) > 0. If so, this sequence with A122535 and
A147812 partition the primes."

We formalize the main claim: the set of primes `prime(k)` with
`prime(k+1)^2 < prime(k) * prime(k+2)` equals the set of primes `prime(k)` with
`prime(k+2) - 2*prime(k+1) + prime(k) > 0` (computed in `ℤ`, so no truncated
subtraction). The partition remark follows formally from this equality, since
A122535 and A147812 are exactly the primes with second difference `= 0`
and `< 0` respectively.

Indexing: OEIS uses `prime(1) = 2`; Mathlib's `Nat.nth Nat.Prime 0 = 2`. We write
`p k = Nat.nth Nat.Prime k` with 0-based `k`; the shift is uniform in `k`, so
the condition on the triple of consecutive primes is unchanged and the
sequences (as sets of primes) are identical (A063535 starts 2, 5, 11, ...).

Reading note: a later OEIS comment (Ya-Ping Lu, 2026) says the conjecture is
true because `b^2 < a*c` implies `a + c > 2*b` (AM-GM). That proves only one
inclusion. The converse is equivalent to: whenever
`g2 := p(k+2) - p(k+1) > g1 := p(k+1) - p(k)`, one has `g1^2 < p(k) * (g2 - g1)`.
This would follow from a prime-gap bound of order `sqrt(2 p)`, which is not known (it is
implied by Cramér/Firoozbakht-type conjectures), so the full statement is still open.
Checked numerically for all consecutive prime triples below 10^8.
-/

namespace OMA.S_oeis_a063535

theorem main :
    {q : ℕ | ∃ k : ℕ, q = Nat.nth Nat.Prime k ∧
        Nat.nth Nat.Prime (k + 1) ^ 2 < Nat.nth Nat.Prime k * Nat.nth Nat.Prime (k + 2)} =
    {q : ℕ | ∃ k : ℕ, q = Nat.nth Nat.Prime k ∧
        (0 : ℤ) < (Nat.nth Nat.Prime (k + 2) : ℤ) - 2 * (Nat.nth Nat.Prime (k + 1) : ℤ)
          + (Nat.nth Nat.Prime k : ℤ)} := by
  sorry

end OMA.S_oeis_a063535
