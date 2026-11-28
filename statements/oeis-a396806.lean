import Mathlib

namespace OMA.S_oeis_a396806

theorem main :
    ∀ (a : ℕ → ℤ) (A : PowerSeries ℚ),
      A = PowerSeries.mk (fun n => (a n : ℚ) / (Nat.factorial n : ℚ)) →
      a 0 = 0 →
      A = PowerSeries.X *
        PowerSeries.subst
          (PowerSeries.subst A (PowerSeries.subst A (PowerSeries.subst A
            (PowerSeries.subst A (PowerSeries.subst A A)))))
          (PowerSeries.exp ℚ) →
      ∀ n : ℕ, 1 ≤ n → (Odd (a n) ↔ Odd n) := by
  sorry

end OMA.S_oeis_a396806
