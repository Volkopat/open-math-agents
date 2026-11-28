import Mathlib

/-!
# A219864: n = p + q with p and 2pq + 1 both prime

Source: https://oeis.org/A219864

A219864 (offset 1): `a(n)` is the number of ways to write `n` as `p + q` with `p` and `2pq + 1`
both prime: 0, 0, 1, 1, 2, 3, 0, 2, 4, 2, …  Here `q = n - p` is a positive integer that need
not be prime (for example `a(3) = 1` comes from `3 = 2 + 1` with `2*2*1 + 1 = 5`).

Conjecture (Zhi-Wei Sun, Nov 30 2012): `a(n) > 0` for all `n > 7`. The entry notes that this has
been verified for `n` up to `3*10^8`.

Since `a(n)` counts the primes `p` with `q = n - p` and `2pq + 1` prime, `a(n) > 0` says exactly
that such a decomposition exists, and the conjecture is stated in that form. The more general
conjectures and guesses of Sun listed afterwards in the entry (with `2pq + m` for other `m`,
for sufficiently large `n`) are separate claims and are not part of this statement.

Conventions: everything is in `ℕ`. No positivity condition on `q` is needed: if `q = 0` then
`2pq + 1 = 1` is not prime.
-/

namespace OMA.S_oeis_a219864

theorem main :
    ∀ n : ℕ, 7 < n → ∃ p q : ℕ, p + q = n ∧ Nat.Prime p ∧ Nat.Prime (2 * p * q + 1) := by
  sorry

end OMA.S_oeis_a219864
