import Mathlib

namespace OMA.S_oeis_a396946

/-- OEIS A396946: Primes `p` such that both Mordell equations `y^2 = x^3 + p^2` and
`y^2 = x^3 - p^2` have nonzero integer solutions (`x ≠ 0` and `y ≠ 0`).
Conjecture: All terms can be expressed in the form `4*m^2 + 1` or `12*m^2 - 1`. -/
theorem main :
    ∀ p : ℕ, Nat.Prime p →
      (∃ x y : ℤ, x ≠ 0 ∧ y ≠ 0 ∧ y ^ 2 = x ^ 3 + (p : ℤ) ^ 2) →
      (∃ x y : ℤ, x ≠ 0 ∧ y ≠ 0 ∧ y ^ 2 = x ^ 3 - (p : ℤ) ^ 2) →
      (∃ m : ℤ, (p : ℤ) = 4 * m ^ 2 + 1 ∨ (p : ℤ) = 12 * m ^ 2 - 1) := by
  sorry

end OMA.S_oeis_a396946
