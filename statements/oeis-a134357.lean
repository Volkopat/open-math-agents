import Mathlib

namespace OMA.S_oeis_a134357

def a005156 (n : ℕ) : ℚ :=
  ∏ k ∈ Finset.range (n - 1),
    (((3 * k + 2 : ℕ) : ℚ) * ((6 * k + 3).factorial : ℚ) * ((2 * k + 1).factorial : ℚ)) /
      (((4 * k + 2).factorial : ℚ) * ((4 * k + 3).factorial : ℚ))

theorem main :
    ∀ n : ℕ, 1 ≤ n →
      (Nat.choose (6 * n - 2) (2 * n) : ℚ) / (2 * (Nat.choose (4 * n - 1) (2 * n) : ℚ)) =
        a005156 (n + 1) / a005156 n := by
  sorry

end OMA.S_oeis_a134357
