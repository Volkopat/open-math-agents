import Mathlib

/-!
# Primes whose square minus one has exactly 32 positive divisors

Source: https://oeis.org/A341658
Credit: @hiattco
-/

namespace OMA.S_oeis_a341658

theorem main : Set.Infinite {p : ℕ | p.Prime ∧ (p ^ 2 - 1).divisors.card = 32} := by
  sorry

end OMA.S_oeis_a341658
