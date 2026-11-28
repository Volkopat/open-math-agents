import Mathlib

/-!
# A282135: Expansion of (Sum_{k = p*q, p prime, q prime} x^k)^3.

Source: https://oeis.org/A282135
Credit: @keiichisince1986-bot

A282135 is the sequence `a(n)` named in the title. The entry states:
Conjecture: a(n) > 0 for n > 15.

Conventions:
- The exponents `k = p q` with `p, q` prime are the semiprimes (squares of primes included). `a(n)` counts
  the ordered ways to write `n` as a sum of three such numbers, so `a(n) > 0` means that `n` is a sum of three
  products of two primes.
-/

namespace OMA.S_oeis_a282135

theorem main :
    ∀ n : ℕ, 15 < n → ∃ p₁ q₁ p₂ q₂ p₃ q₃ : ℕ, p₁.Prime ∧ q₁.Prime ∧ p₂.Prime ∧ q₂.Prime ∧
      p₃.Prime ∧ q₃.Prime ∧ p₁ * q₁ + p₂ * q₂ + p₃ * q₃ = n := by
  sorry

end OMA.S_oeis_a282135
