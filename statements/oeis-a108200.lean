import Mathlib

namespace OMA.S_oeis_a108200

/-- The conjecture from OEIS A108200, using the golden semiprimes of A108540. -/
theorem main :
    ∀ n : ℕ, 4 < n →
      ∃ k : ℕ, 0 < k ∧ k < n ^ (n / 2) ∧
        ∃ p q : ℕ, Nat.Prime p ∧ Nat.Prime q ∧ k * n + 1 = p * q ∧
          |(p : ℝ) * ((1 + Real.sqrt 5) / 2) - (q : ℝ)| < 1 := by
  sorry

end OMA.S_oeis_a108200
