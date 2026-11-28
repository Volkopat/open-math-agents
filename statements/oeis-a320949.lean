import Mathlib

namespace OMA.S_oeis_a320949

theorem main :
    ∀ a : ℕ → ℤ,
      a 0 = 1 →
      ∀ B : PowerSeries ℚ,
        B * (1 + PowerSeries.mk (fun k => (a k : ℚ))) = 1 →
        (∀ k : ℕ,
          HasSum (fun n : ℕ =>
            ((PowerSeries.coeff k ((1 + PowerSeries.X) ^ (n ^ 2) * B ^ (n + 1)) : ℚ) : ℝ))
            (if k = 0 then 1 else 0)) →
        ∀ k : ℕ, 0 < k → (3 : ℤ) ∣ a k := by
  sorry

end OMA.S_oeis_a320949
