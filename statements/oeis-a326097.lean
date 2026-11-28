import Mathlib

namespace OMA.S_oeis_a326097

theorem main :
    ∀ a : ℕ → ℤ,
      a 0 = 1 →
      (∀ k : ℕ,
        let A : PowerSeries ℚ := PowerSeries.mk (fun n => (a n : ℚ) / (Nat.factorial n : ℚ))
        ∑ n ∈ Finset.range (k + 1),
          (1 / (Nat.factorial n : ℚ)) *
            PowerSeries.coeff k (((1 + PowerSeries.X) ^ n - A) ^ n) =
        if k = 0 then 1 else 0) →
      ∀ k : ℕ, 3 < k → (a k % 2 = 1 ↔ k % 4 = 2) := by
  sorry

end OMA.S_oeis_a326097
