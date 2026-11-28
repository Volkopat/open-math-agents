import Mathlib

namespace OMA.S_oeis_a345652

theorem main :
    ∀ a : ℕ → ℤ,
      a 0 = 1 →
      (let A : PowerSeries ℚ := PowerSeries.mk (fun n => (a n : ℚ) / (Nat.factorial n : ℚ))
       let Eneg : PowerSeries ℚ := PowerSeries.mk (fun n => (-1 : ℚ) ^ n / (Nat.factorial n : ℚ))
       PowerSeries.derivative ℚ A = (-PowerSeries.X * Eneg) * A) →
      ∀ p : ℕ, Nat.Prime p →
        a p ^ 2 ≡ 1 [ZMOD (p : ℤ)] := by
  sorry

end OMA.S_oeis_a345652
