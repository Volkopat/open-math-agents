import Mathlib

/-!
# A230254: n = p + q with p and (p+1)*q/2 + 1 both prime

Source: https://oeis.org/A230254

A230254 (offset 1): `a(n)` is the number of ways to write `n = p + q` with `p` and
`(p+1)*q/2 + 1` both prime. For example `a(15) = 1` since `15 = 5 + 10` with `5` and
`(5+1)*10/2 + 1 = 31` both prime, and `a(30) = 1` since `30 = 2 + 28` with `2` and
`(2+1)*28/2 + 1 = 43` both prime.

Conjecture (Zhi-Wei Sun, Oct 14 2013): `a(n) > 0` for all `n > 3`. The entry notes that this has
been verified for `n` up to `10^8`.

Since `a(n)` counts the primes `p` such that, with `q = n - p`, the number `(p+1)*q/2 + 1` is
prime, `a(n) > 0` says exactly that such a decomposition exists, and the conjecture is stated in
that form. The similar conjectures mentioned afterwards in the entry (for example with
`(p+1)*q/2 - 1`) are separate claims and are not part of this statement.

Conventions:
- `(p+1)*q/2` is the exact rational quotient, so `(p+1)*q/2 + 1` can only be prime when
  `(p+1)*q` is even (this matters only for `p = 2` with `q` odd). The hypothesis
  `2 ∣ (p + 1) * q` records this, so that the natural-number division below is exact; the listed
  terms of A230254 are reproduced with this reading and not with floor division.
- `q = n - p` is a positive integer, not required to be prime. No positivity condition is
  needed: `q = 0` gives `(p+1)*q/2 + 1 = 1`, which is not prime.
-/

namespace OMA.S_oeis_a230254

theorem main :
    ∀ n : ℕ, 3 < n →
      ∃ p q : ℕ, p + q = n ∧ Nat.Prime p ∧ 2 ∣ (p + 1) * q ∧
        Nat.Prime ((p + 1) * q / 2 + 1) := by
  sorry

end OMA.S_oeis_a230254
