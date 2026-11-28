import Mathlib.RingTheory.PowerSeries.Derivative

/-!
# Paul D. Hanna's parity conjecture for OEIS A301933

Source: https://oeis.org/A301933
Credit: @anmolspace

Hanna's ordinary generating series begins x + 3x² + 24x³ + 291x⁴.
The denominator in the defining quotient has constant coefficient one, so
cross-multiplication gives the same equation in the integer power series ring.
-/

namespace OMA.S_oeis_a301933

open PowerSeries

/-- The normalized integer series in Hanna's differential equation. -/
def Defines (A : PowerSeries ℤ) : Prop :=
  A.constantCoeff = 0 ∧ coeff 1 A = 1 ∧
    A * (1 + A * d⁄dX ℤ A) = X * (1 + 4*A*d⁄dX ℤ A)

/-- A normalized solution exists. In each such solution the odd coefficients
of both A and the related series A·A′ occur exactly at 1, 2, 4, 8, and so on. -/
theorem main : (∃ A, Defines A) ∧
    ∀ A, Defines A → ∀ n : ℕ, 0 < n →
      (Odd (coeff n A) ↔ ∃ k : ℕ, n = 2^k) ∧
      (Odd (coeff n (A * d⁄dX ℤ A)) ↔ ∃ k : ℕ, n = 2^k) := by
  sorry

end OMA.S_oeis_a301933
