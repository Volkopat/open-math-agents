import Mathlib.RingTheory.PowerSeries.Basic
import Mathlib.RingTheory.PowerSeries.Derivative

namespace OMA.S_oeis_a337948

/-- OEIS A337948: Let `S(x) = 1 + ∑_{m≥1} (-1)^m * (2^m + 1) * 2^(m*(m-1)/2) * x^(m^2) ∈ ℤ[[x]]`
(which equals `∑_{n=-∞}^∞ (-√2)^n * (√2 * x)^(n^2)`), and let `A(x) = ∑_{n≥1} a(n) * x^n ∈ ℤ[[x]]`
satisfy `A(x) * S(x) = -x * S'(x)` (the logarithmic derivative of `-log S(x)`).
Then `3 ∣ a(4*n + 1)`, `3 ∣ a(4*n + 2)`, and `3 ∣ a(4*n + 3)` for all `n ≥ 0`. -/
theorem main :
    ∀ (A S : PowerSeries ℤ),
      PowerSeries.constantCoeff S = 1 →
      (∀ r : ℕ, 1 ≤ r → PowerSeries.coeff r S =
        ∑ m ∈ Finset.Icc 1 r,
          if m ^ 2 = r then (-1 : ℤ) ^ m * (2 ^ m + 1) * 2 ^ (m * (m - 1) / 2) else 0) →
      A * S = -PowerSeries.X * PowerSeries.derivative ℤ S →
      ∀ n : ℕ, (3 : ℤ) ∣ PowerSeries.coeff (4 * n + 1) A ∧
               (3 : ℤ) ∣ PowerSeries.coeff (4 * n + 2) A ∧
               (3 : ℤ) ∣ PowerSeries.coeff (4 * n + 3) A := by
  sorry

end OMA.S_oeis_a337948
