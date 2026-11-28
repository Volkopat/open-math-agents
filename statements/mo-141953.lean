import Mathlib

/-!
# On the prime divisors of two numbers

BHZ asked whether two odd prime powers can satisfy both prime-divisor-set
equalities below and conjectured that this is impossible.
Source: https://mathoverflow.net/questions/141953
Lean statement by @jacklarmer.
-/

namespace OMA.S_mo_141953

theorem main :
    ∀ p p' a b : ℕ, p.Prime → p'.Prime → p % 4 = 1 → p' % 4 = 1 →
      0 < a → 0 < b →
      let q := p ^ a
      let q' := p' ^ b
      p ∣ q' ^ 2 + 1 → p' ∣ q ^ 2 + 1 →
        ¬ ((q ^ 2 - 1).primeFactors = (q' ^ 2 - 1).primeFactors ∧
          insert p (q ^ 2 + 1).primeFactors = insert p' (q' ^ 2 + 1).primeFactors) := by
  sorry

end OMA.S_mo_141953
