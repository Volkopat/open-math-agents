import Mathlib.RingTheory.PowerSeries.Basic
import Mathlib.RingTheory.PowerSeries.Inverse

namespace OMA.S_oeis_a380066

/-- OEIS A380066: Let A(x) ∈ ℤ[[x]] have A(0) = 1 and satisfy
1/2 = ∑_{n=-∞}^∞ x^n * A(x)^n * (A(x)^n + x)^(n - 1) * (A(x) + x^n)^(n - 1).
Clearing the 
 = 0 denominator 2 * (1 + x) * (A(x) + 1) yields
(1 + x) * (A(x) + 1) = 2 + 2 * (1 + x) * (A(x) + 1) * ∑_{n≥1} (T_+(n) + T_-(n))
(expressed coefficient-wise by the finite sum up to 
). Then (r) % 4 = 2 for all 
 > 0. -/
theorem main :
    ∀ (A : PowerSeries ℤ),
      PowerSeries.constantCoeff A = 1 →
      (∀ r : ℕ,
        PowerSeries.coeff r ((1 + PowerSeries.X) * (A + 1)) =
          (if r = 0 then 2 else 0) +
          2 * ∑ n ∈ Finset.Icc 1 r,
            PowerSeries.coeff r
              ((1 + PowerSeries.X) * (A + 1) *
                (PowerSeries.X ^ n * A ^ n * (A ^ n + PowerSeries.X) ^ (n - 1) *
                    (A + PowerSeries.X ^ n) ^ (n - 1) +
                  PowerSeries.X ^ (n ^ 2) * A ^ (n ^ 2) *
                    (Ring.inverse (1 + PowerSeries.X * A ^ n)) ^ (n + 1) *
                    (Ring.inverse (1 + PowerSeries.X ^ n * A)) ^ (n + 1)))) →
      ∀ r : ℕ, 0 < r → PowerSeries.coeff r A % 4 = 2 := by
  sorry

end OMA.S_oeis_a380066
