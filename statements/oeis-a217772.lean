import Mathlib

namespace OMA.S_oeis_a217772

theorem main :
    ∀ p : ℕ, Nat.Prime p → Odd p →
      3 * p ^ 3 ∣ ((p + 1) * Nat.factorial (3 * p) /
        (Nat.factorial (2 * p - 1) * Nat.factorial (p + 1) * (2 * p)) - 3) := by
  sorry

end OMA.S_oeis_a217772
