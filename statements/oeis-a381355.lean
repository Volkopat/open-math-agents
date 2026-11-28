import Mathlib

namespace OMA.S_oeis_a381355

/-- The `n`-th prime (1-indexed: `nthPrime1 1 = 2`, `nthPrime1 2 = 3`, ...). -/
noncomputable def nthPrime1 (n : ℕ) : ℕ :=
  Nat.nth Nat.Prime (n - 1)

theorem main :
    ∀ (A F : PowerSeries ℤ),
      PowerSeries.constantCoeff F = 1 →
      A * F = PowerSeries.X * PowerSeries.derivative ℤ F →
      (∀ n : ℕ, 1 < n → PowerSeries.coeff n (F ^ nthPrime1 n) = 0) →
      ∀ n : ℕ, 1 < n → (nthPrime1 n : ℤ) ∣ PowerSeries.coeff n A := by
  sorry

end OMA.S_oeis_a381355
