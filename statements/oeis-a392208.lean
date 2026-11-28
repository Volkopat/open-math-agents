import Mathlib

namespace OMA.S_oeis_a392208

theorem main :
    ∀ (a : ℕ → ℤ) (A : PowerSeries ℚ),
      A = PowerSeries.mk (fun n => (a n : ℚ) / (Nat.factorial n : ℚ)) →
      a 0 = 0 →
      PowerSeries.derivative ℚ A =
        PowerSeries.subst (A * (PowerSeries.derivative ℚ A) ^ 3) (PowerSeries.exp ℚ) →
      ∀ n : ℕ, 1 ≤ n → (Even (a n) ↔ 3 ∣ n) := by
  sorry

end OMA.S_oeis_a392208
