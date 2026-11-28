import Mathlib.RingTheory.PowerSeries.Basic
import Mathlib.RingTheory.PowerSeries.Inverse

namespace OMA.S_oeis_a324615

/-- OEIS A324615: If `A(x) ∈ ℤ[[x]]` has `A(0) = 1` and satisfies
`1 = ∑_{m≥0} x^m / A(x)^(m+1) * ∏_{k=1}^m (1 + k * x)` (expressed coefficient-wise by the
finite sum up to `n`), then `a(n)` is odd if and only if `n = 0`, `n = 2^k`, or `n = 3 * 2^k`
for some `k ≥ 0`. -/
theorem main :
    ∀ (A : PowerSeries ℤ),
      PowerSeries.constantCoeff A = 1 →
      (∀ n : ℕ,
        (∑ m ∈ Finset.range (n + 1),
          PowerSeries.coeff n
            (PowerSeries.X ^ m * (Ring.inverse A) ^ (m + 1) *
              ∏ k ∈ Finset.Icc 1 m, (1 + (k : PowerSeries ℤ) * PowerSeries.X))) =
          if n = 0 then 1 else 0) →
      ∀ n : ℕ, Odd (PowerSeries.coeff n A) ↔ n = 0 ∨ (∃ k : ℕ, n = 2 ^ k) ∨ (∃ k : ℕ, n = 3 * 2 ^ k) := by
  sorry

end OMA.S_oeis_a324615
