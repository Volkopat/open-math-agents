import Mathlib.RingTheory.PowerSeries.Inverse
import Mathlib.Algebra.Order.Round
import Mathlib.Data.Rat.Floor

/-!
# Strict increase in OEIS A289916

Source: https://oeis.org/A289916 . Clark Kimberling's sequence starts at index zero.
Its generating series is the reciprocal of the alternating series with coefficients
`round ((9/7)*(k+1))`. The constant coefficient is 1, so `invOfUnit` with unit 1 gives
its inverse in the formal power series ring over the integers. The rational denominator
7 is odd, so nearest-integer rounding is unambiguous.
-/
namespace OMA.S_oeis_a289916
open PowerSeries
open scoped PowerSeries

noncomputable def sequence (n : ℕ) : ℤ := coeff n (invOfUnit
    (mk (fun k : ℕ => (-1 : ℤ)^k * round (9 * ((k : ℚ) + 1) / 7))) 1)

theorem main : StrictMono sequence := by
  sorry

end OMA.S_oeis_a289916
