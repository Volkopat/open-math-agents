import Mathlib

/-!
# A306996: Number of primes q < prime(n) such that 4*prime(n) + q is prime

Source: https://oeis.org/A306996

Conjecture (OEIS A306996):
For every `n ≥ 3` (equivalently, for every prime `p ≥ 5`), there is at least one
prime `q < p` such that `4 * p + q` is prime (i.e., `a(n) > 0`).

Conventions:
- Offset: `1`; first terms: `a(1) = 0` (`p = 2`), `a(2) = 0` (`p = 3`), `a(3) = 1` (`p = 5`),
  `a(4) = 1` (`p = 7`), `a(5) = 1` (`p = 11`), `a(6) = 1` (`p = 13`), `a(7) = 3` (`p = 17`), ...
- Quantifying directly over primes `p ≥ 5` is equivalent to `n ≥ 3` since `prime(3) = 5`.
-/

namespace OMA.S_oeis_a306996

/-- Number of primes `q < p` such that `4 * p + q` is prime (OEIS A306996 at `p = prime(n)`). -/
def countPrimes (p : ℕ) : ℕ :=
  ((Finset.range p).filter (fun q => Nat.Prime q ∧ Nat.Prime (4 * p + q))).card

/-- Conjecture: `countPrimes p > 0` for every prime `p ≥ 5` (i.e., `a(n) > 0` for `n ≥ 3`). -/
theorem main :
    ∀ p : ℕ, Nat.Prime p → 5 ≤ p → 0 < countPrimes p := by
  sorry

end OMA.S_oeis_a306996
