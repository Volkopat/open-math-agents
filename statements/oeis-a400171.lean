import Mathlib.Data.Nat.Squarefree
import Mathlib.NumberTheory.Primorial

/-!
# A400171 and the primorial-base logarithm

The arithmetic derivative is expanded over the distinct prime factors of k.
The primorial-base logarithm is completely additive and takes a prime p to
the product of the primes strictly below p.

Sources: https://oeis.org/A400171, https://oeis.org/A003415, https://oeis.org/A276085
-/

namespace OMA.S_oeis_a400171

def arithmeticDerivative (k : ℕ) : ℕ :=
  ∑ p ∈ k.primeFactors, k.factorization p * (k / p)

def primorialLog (k : ℕ) : ℕ :=
  ∑ p ∈ k.primeFactors, k.factorization p * primorial (p - 1)

theorem main : ∀ k : ℕ, 1 < k →
    (∀ p : ℕ, p.Prime → ¬ p ^ p ∣ k) →
    primorialLog k ∣ arithmeticDerivative k →
    (arithmeticDerivative k / primorialLog k = 1 ↔ Squarefree k) := by
  sorry

end OMA.S_oeis_a400171
