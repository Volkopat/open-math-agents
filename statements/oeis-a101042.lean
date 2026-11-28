import Mathlib

/-!
# A101042: a(n) is the smallest positive d such that the n-th prime is the smallest prime p for which p+d is also prime.

Source: https://oeis.org/A101042
Credit: @keiichisince1986-bot

A101042 is the sequence `a(n)` named in the title. The entry states:
It is conjectured that a(n) always exists. a(386) is the first number which must be above 10^12.

Conventions:
- `n` ranges over all primes `q = prime(n)`. `a(n)` exists means: some `d > 0` has `q + d` prime and
  `p + d` composite (not prime) for every prime `p < q`.
-/

namespace OMA.S_oeis_a101042

theorem main :
    ∀ q : ℕ, q.Prime → ∃ d : ℕ, 0 < d ∧ (q + d).Prime ∧ ∀ p : ℕ, p.Prime → p < q → ¬ (p + d).Prime := by
  sorry

end OMA.S_oeis_a101042
