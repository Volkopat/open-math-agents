import Mathlib.RingTheory.PowerSeries.Basic
import Mathlib.RingTheory.PowerSeries.Inverse
import Mathlib.RingTheory.PowerSeries.Substitution

namespace OMA.S_oeis_a300734

/-- OEIS A300734: If A(x) ∈ ℤ[[x]] has A(0) = 1, (1) = 1, and satisfies
[x^n] A(x / A(x)^(2 * n^2)) = 0 for all 
 > 1, then n ^ 2 divides (n) for all 
 ≥ 1. -/
theorem main :
    ∀ (A : PowerSeries ℤ),
      PowerSeries.constantCoeff A = 1 →
      PowerSeries.coeff 1 A = 1 →
      (∀ n : ℕ, 1 < n →
        PowerSeries.coeff n (PowerSeries.subst (PowerSeries.X * (Ring.inverse A) ^ (2 * n ^ 2)) A) = 0) →
      ∀ n : ℕ, 1 ≤ n → ((n ^ 2 : ℕ) : ℤ) ∣ PowerSeries.coeff n A := by
  sorry

end OMA.S_oeis_a300734
