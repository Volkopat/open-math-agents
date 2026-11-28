import Mathlib

namespace OMA.S_oeis_a277403

theorem main :
    ∀ (a : ℕ → ℤ) (A I : PowerSeries ℚ),
      A = PowerSeries.mk (fun n => (a n : ℚ) / (Nat.factorial n : ℚ)) →
      a 0 = 0 →
      PowerSeries.constantCoeff I = 0 →
      PowerSeries.derivative ℚ I = A →
      PowerSeries.subst (PowerSeries.X - I) A = PowerSeries.X + I →
      ∀ n : ℕ, 2 < n → (10 : ℤ) ∣ a n := by
  sorry

end OMA.S_oeis_a277403
