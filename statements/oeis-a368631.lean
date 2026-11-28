import Mathlib

namespace OMA.S_oeis_a368631

theorem main :
    ∀ (a : ℕ → ℤ) (A B : PowerSeries ℚ),
      A = PowerSeries.mk (fun n => (a n : ℚ) / (Nat.factorial n : ℚ)) →
      a 0 = 1 →
      A * B = 1 →
      PowerSeries.subst (PowerSeries.X * B) A =
        PowerSeries.subst (PowerSeries.X * A ^ 2) (PowerSeries.exp ℚ) →
      ∀ n : ℕ, a n % 3 = 1 := by
  sorry

end OMA.S_oeis_a368631
