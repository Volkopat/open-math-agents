import Mathlib.RingTheory.PowerSeries.Derivative
import Mathlib.Data.Nat.Choose.Basic

/-!
# A051286: differential equation for the ordinary generating function

The coefficients use Paul D. Hanna's binomial-square formula for A051286.
The formal power series equation is Emanuele Munarini's December 2017
form of the recurrence conjectured by R. J. Mathar.

Source: https://oeis.org/A051286
-/

namespace OMA.S_oeis_a051286

open Finset PowerSeries

def a (n : ℕ) : ℕ :=
  ∑ k ∈ range (n + 1), ((n - k).choose k) ^ 2

def A : PowerSeries ℚ :=
  PowerSeries.mk fun n => (a n : ℚ)

theorem main :
    (1 - C 2 * X - X ^ 2 - C 2 * X ^ 3 + X ^ 4) * derivative ℚ A =
      (1 + X + C 3 * X ^ 2 - C 2 * X ^ 3) * A := by
  sorry

end OMA.S_oeis_a051286
