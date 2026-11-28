import Mathlib.RingTheory.PowerSeries.Basic
import Mathlib.RingTheory.PowerSeries.Inverse

namespace OMA.S_oeis_a379202

/-- OEIS A379202: Let `A(x) ∈ ℤ[[x]]` have `A(0) = 0`, `a(1) = 1`, and satisfy
`1/x = ∑_{n=-∞}^∞ A(x)^n * (A(x)^n + 2)^(n + 1)`. Multiplying by `x * A(x)` and pairing
`n ≥ 0` with `-(n + 2)` yields
`A(x) = x + x * ∑_{n≥0} (A(x)^(n+1) * (A(x)^n + 2)^(n+1) + A(x)^((n+1)^2) / (1 + 2 * A(x)^(n+2))^(n+1))`
(expressed coefficient-wise by the finite sum up to `k`). Then `a(k)` is even for all `k > 1`. -/
theorem main :
    ∀ (A : PowerSeries ℤ),
      PowerSeries.constantCoeff A = 0 →
      PowerSeries.coeff 1 A = 1 →
      (∀ k : ℕ, 1 ≤ k →
        PowerSeries.coeff k A =
          (if k = 1 then 1 else 0) +
          ∑ n ∈ Finset.range k,
            PowerSeries.coeff (k - 1)
              (A ^ (n + 1) * (A ^ n + 2) ^ (n + 1) +
                A ^ ((n + 1) ^ 2) * (Ring.inverse (1 + 2 * A ^ (n + 2))) ^ (n + 1))) →
      ∀ k : ℕ, 1 < k → Even (PowerSeries.coeff k A) := by
  sorry

end OMA.S_oeis_a379202
