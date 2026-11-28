import Mathlib

/-!
# Prime divisors of Bernoulli numerators at twice a prime

Chai Wah Wu conjectured that every prime p greater than three divides the
numerator of the Bernoulli number with index 2p. This implies the upper bound
for the least prime factor stated in the entry.

Source: https://oeis.org/A332300.
-/
namespace OMA.S_oeis_a332300
theorem main : ∀ p : ℕ, p.Prime → 3 < p → (p:ℤ) ∣ (bernoulli (2*p)).num := by
  sorry
end OMA.S_oeis_a332300
