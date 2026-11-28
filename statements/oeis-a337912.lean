import Mathlib.RingTheory.PowerSeries.Basic

namespace OMA.S_oeis_a337912

/-- OEIS A337912: If `A(x) ∈ ℤ[[x]]` has `A(0) = 1` and satisfies
`∑_{n≥0} x^n * A(x)^(n*(n-1)/2) + ∑_{n≥0} (-x)^n * A(x)^(n*(n+1)/2) = 2`
(expressed coefficient-wise by the finite sum up to `k`), then `a(2*n) % 16 = 0` for all `n > 1`
and `a(2*n + 1) % 16 = 8` for all `n > 0`. -/
theorem main :
    ∀ (A : PowerSeries ℤ),
      PowerSeries.constantCoeff A = 1 →
      (∀ k : ℕ,
        (∑ n ∈ Finset.range (k + 1),
          PowerSeries.coeff k
            (PowerSeries.X ^ n * A ^ (n * (n - 1) / 2) +
              (-PowerSeries.X) ^ n * A ^ (n * (n + 1) / 2))) =
          if k = 0 then 2 else 0) →
      (∀ n : ℕ, 1 < n → PowerSeries.coeff (2 * n) A % 16 = 0) ∧
      (∀ n : ℕ, 0 < n → PowerSeries.coeff (2 * n + 1) A % 16 = 8) := by
  sorry

end OMA.S_oeis_a337912
