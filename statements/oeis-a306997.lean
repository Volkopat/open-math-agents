import Mathlib

/-!
# A306997: Number of primes q < prime(n) such that 6*prime(n) + q is prime

Source: https://oeis.org/A306997

Conjecture (OEIS A306997):
For every `n ≥ 4` (equivalently, for every prime `p ≥ 7`), there is at least one
prime `q < p` such that `6 * p + q` is prime (i.e., `a(n) > 0`).

Conventions:
- Offset: `1`; first terms: `a(1) = 0` (`p = 2`), `a(2) = 0` (`p = 3`), `a(3) = 0` (`p = 5`),
  `a(4) = 1` (`p = 7`), `a(5) = 2` (`p = 11`), `a(6) = 2` (`p = 13`), `a(7) = 3` (`p = 17`), ...
- Quantifying directly over primes `p ≥ 7` is equivalent to `n ≥ 4` since `prime(4) = 7`.
-/

namespace OMA.S_oeis_a306997

/-- Number of primes `q < p` such that `6 * p + q` is prime (OEIS A306997 at `p = prime(n)`). -/
def countPrimes (p : ℕ) : ℕ :=
  ((Finset.range p).filter (fun q => Nat.Prime q ∧ Nat.Prime (6 * p + q))).card

/-- Conjecture: `countPrimes p > 0` for every prime `p ≥ 7` (i.e., `a(n) > 0` for `n ≥ 4`). -/
theorem main :
    ∀ p : ℕ, Nat.Prime p → 7 ≤ p → 0 < countPrimes p := by
  sorry

end OMA.S_oeis_a306997
