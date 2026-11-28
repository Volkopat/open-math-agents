import Mathlib

namespace OMA.S_oeis_a325286

theorem main :
    ∀ a : ℕ → ℤ,
      a 0 = 1 →
      ∀ B : PowerSeries ℚ,
        B * PowerSeries.mk (fun k => (a k : ℚ)) = 1 →
        (∀ k : ℕ,
          HasSum (fun n : ℕ =>
            ((PowerSeries.coeff k ((1 + PowerSeries.X) ^ (n * (n - 1) / 2) * B ^ n) : ℚ) : ℝ) /
              2 ^ (n + 1))
            (if k = 0 then 1 else 0)) →
        ∀ k : ℕ, a k % 3 = if (∀ d ∈ Nat.digits 3 k, d ≠ 2) then 1 else 0 := by
  sorry

end OMA.S_oeis_a325286
