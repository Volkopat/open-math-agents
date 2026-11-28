import Mathlib.RingTheory.PowerSeries.Derivative
import Mathlib.Data.ZMod.Basic

/-!
# OEIS A397588

Paul D. Hanna's ordinary generating series starts with X and satisfies
A = X + (X A²)'. The conjecture says its positive-index coefficient is
odd exactly when the index is a power of two. Reduction to ZMod 2
expresses oddness of an integer coefficient.

Source: https://oeis.org/A397588
Formalization: @ecirak42.
-/

namespace OMA.S_oeis_a397588

theorem main : ∀ A : PowerSeries ℤ, A.coeff 0 = 0 →
    A = PowerSeries.X + PowerSeries.derivative ℤ (PowerSeries.X * A ^ 2) →
    ∀ n : ℕ, 1 ≤ n → (((A.coeff n : ℤ) : ZMod 2) = 1 ↔ ∃ k : ℕ, n = 2 ^ k) := by
  sorry

end OMA.S_oeis_a397588
