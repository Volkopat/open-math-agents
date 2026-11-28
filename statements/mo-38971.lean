import Mathlib

namespace OMA.S_mo_38971

/-- For a positive base that is not a power of ten, is the greatest exponent
under a decimal digit sum bound at most linear in that bound? -/
theorem main :
    ∀ a : ℕ, 0 < a → (∀ m : ℕ, a ≠ 10 ^ m) →
      ∃ C N : ℕ, 0 < C ∧
        ∀ s ≥ N, ∀ k : ℕ, (Nat.digits 10 (a ^ k)).sum ≤ s → k ≤ C * s := by
  sorry

end OMA.S_mo_38971
