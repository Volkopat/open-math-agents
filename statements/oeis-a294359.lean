import Mathlib.RingTheory.PowerSeries.Basic
import Mathlib.RingTheory.PowerSeries.Inverse
import Mathlib.RingTheory.PowerSeries.Substitution

namespace OMA.S_oeis_a294359

/-- OEIS A294359: Let `F(x) ∈ ℤ[[x]]` have `F(0) = 1` and satisfy `F(x) = F(x^2) + x * F(x^4)`
(the generating function of the Fibbinary numbers A003714). Then for all `n ≥ 1`,
`a(n) = [x^n] (1 / F(x))^((n + 1)^2)` is even. -/
theorem main :
    ∀ (F : PowerSeries ℤ),
      PowerSeries.constantCoeff F = 1 →
      F = PowerSeries.subst (PowerSeries.X ^ 2) F +
          PowerSeries.X * PowerSeries.subst (PowerSeries.X ^ 4) F →
      ∀ n : ℕ, 1 ≤ n → Even (PowerSeries.coeff n ((Ring.inverse F) ^ ((n + 1) ^ 2))) := by
  sorry

end OMA.S_oeis_a294359
