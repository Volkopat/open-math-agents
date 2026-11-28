import Mathlib

/-!
# Infinitude of OEIS A236423

Thomas Ordowski's sequence consists of the positive integers `k` for which
every factorization `k = m * d` into positive integers yields a prime `m² + d²`.
The entry conjectures that this set is infinite. Charles R. Greathouse IV
observes separately that Schinzel's Hypothesis H would imply the conjecture.

Source: https://oeis.org/A236423
Credit: @studer

-/

namespace OMA.S_oeis_a236423

theorem main :
    Set.Infinite {k : ℕ | 0 < k ∧ ∀ m ∈ k.divisors, Nat.Prime (m ^ 2 + (k / m) ^ 2)} := by
  sorry

end OMA.S_oeis_a236423
