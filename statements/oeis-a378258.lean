import Mathlib

namespace OMA.S_oeis_a378258

theorem main :
    ∀ (A B : PowerSeries ℤ),
      PowerSeries.constantCoeff A = 0 →
      PowerSeries.coeff 1 A = 1 →
      A = B + PowerSeries.C (5 : ℤ) * A ^ 2 →
      PowerSeries.subst (A - A ^ 2) B = PowerSeries.X →
      ∀ n : ℕ, 1 ≤ n → (Odd (PowerSeries.coeff n A) ↔ ∃ k : ℕ, n = 2 ^ k) := by
  sorry

end OMA.S_oeis_a378258
