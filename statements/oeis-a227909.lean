import Mathlib

/-!
# A227909: 2n = p + q with p, q and (p-1)*(q+1) - 1 all prime

Source: https://oeis.org/A227909

A227909 (offset 1): `a(n)` is the number of ways to write `2*n = p + q` with `p`, `q` and
`(p-1)*(q+1) - 1` all prime. For example `a(6) = 1` since `12 = 5 + 7` and
`(5-1)*(7+1) - 1 = 31` is prime.

Conjecture (Olivier Gérard and Zhi-Wei Sun, Oct 13 2013): `a(n) > 0` for all `n > 1`. The entry
notes that this is stronger than Goldbach's conjecture for even numbers and that it has been
verified for `n` up to `10^9` (Mauro Fiorentini, Jul 26 2023).

Since `a(n)` counts the decompositions `2n = p + q` with `p`, `q`, `(p-1)*(q+1) - 1` all prime,
`a(n) > 0` says exactly that such a decomposition exists, and the conjecture is stated in that
form.

Conventions:
- The condition is not symmetric in `p` and `q`, and the decompositions are ordered: the listed
  terms of A227909 are reproduced by counting all primes `p` with `q = 2n - p`, with no
  requirement `p ≤ q`. Accordingly no ordering between `p` and `q` is imposed.
- Everything is in `ℕ`. Both `p - 1` and the final `- 1` are exact subtractions, since `p ≥ 2`
  and `q ≥ 2` give `(p-1)*(q+1) ≥ 3`.
-/

namespace OMA.S_oeis_a227909

theorem main :
    ∀ n : ℕ, 1 < n →
      ∃ p q : ℕ, p + q = 2 * n ∧ Nat.Prime p ∧ Nat.Prime q ∧
        Nat.Prime ((p - 1) * (q + 1) - 1) := by
  sorry

end OMA.S_oeis_a227909
