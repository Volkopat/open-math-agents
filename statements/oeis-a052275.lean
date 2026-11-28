import Mathlib.Data.ZMod.Defs
import Mathlib.SetTheory.Cardinal.Finite
import Mathlib.RingTheory.PowerSeries.Basic

namespace OMA.S_oeis_a052275

/-- OEIS A052275: number of distinct 6th powers modulo `n`. -/
noncomputable def a052275 (n : ℕ) : ℕ :=
  Nat.card (Set.range (fun x : ZMod n => x ^ 6))

/-- OEIS A052275 conjectures (R. J. Mathar):
1. `∑_{n ≥ 0} a(2^n) x^n = (1 - 2x^2 - 2x^3 - x^4 - x^5 - 2x^6) / ((x - 1)(2x - 1)(1 + x)(1 + x + x^2)(x^2 - x + 1))`;
2. `∑_{n ≥ 0} a(3^n) x^n = (1 - x - 4x^2 - 2x^3 - 2x^4 - 2x^5 - 3x^6) / ((x - 1)(3x - 1)(1 + x)(x^2 - x + 1)(1 + x + x^2))`. -/
theorem main :
    (PowerSeries.mk (fun n => (a052275 (2 ^ n) : ℤ))) *
        ((PowerSeries.X - 1) * (2 * PowerSeries.X - 1) * (1 + PowerSeries.X) *
          (1 + PowerSeries.X + PowerSeries.X ^ 2) * (PowerSeries.X ^ 2 - PowerSeries.X + 1)) =
      1 - 2 * PowerSeries.X ^ 2 - 2 * PowerSeries.X ^ 3 - PowerSeries.X ^ 4 -
        PowerSeries.X ^ 5 - 2 * PowerSeries.X ^ 6 ∧
    (PowerSeries.mk (fun n => (a052275 (3 ^ n) : ℤ))) *
        ((PowerSeries.X - 1) * (3 * PowerSeries.X - 1) * (1 + PowerSeries.X) *
          (PowerSeries.X ^ 2 - PowerSeries.X + 1) * (1 + PowerSeries.X + PowerSeries.X ^ 2)) =
      1 - PowerSeries.X - 4 * PowerSeries.X ^ 2 - 2 * PowerSeries.X ^ 3 -
        2 * PowerSeries.X ^ 4 - 2 * PowerSeries.X ^ 5 - 3 * PowerSeries.X ^ 6 := by
  sorry

end OMA.S_oeis_a052275
