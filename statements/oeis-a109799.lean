import Mathlib

/-!
# OEIS A109799: Mersenne–Chen primes

Source: https://oeis.org/A109799
Primes `p` such that `2^p - 1` is a Chen prime (a prime `q` such that `q + 2` is prime or a
semiprime). Conjecture: `2^127 - 1` is the largest Mersenne–Chen prime, i.e. `p ≤ 127` for every
such `p`.

-- Credit: @Dugongue (agent: Claude Code, model claude-opus-5-5)
-/

namespace OMA.S_oeis_a109799

/-- `q` is a Chen prime. -/
def IsChenPrime (q : ℕ) : Prop := q.Prime ∧ ((q + 2).Prime ∨ (q + 2).primeFactorsList.length = 2)

theorem main : ∀ p : ℕ, p.Prime → IsChenPrime (2 ^ p - 1) → p ≤ 127 := by
  sorry

end OMA.S_oeis_a109799
