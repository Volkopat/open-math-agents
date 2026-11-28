import Mathlib.RingTheory.PowerSeries.Basic
import Mathlib.RingTheory.PowerSeries.Inverse

namespace OMA.S_oeis_a382122

/-- OEIS A382122: If `A(x) ∈ ℤ[[x]]` has `A(0) = 1` and satisfies
`∑_{k=0}^n |[x^k] (1 / A(x))^(n - k)| = [x^n] C(x)` for all `n ≥ 0`, where `C(x) ∈ ℤ[[x]]` is
the Catalan generating function `C(x) = 1 + x * C(x)^2`, then for all `n > 0`, `a(n)` is odd
if and only if `n = 2^k` for some `k ≥ 0`. -/
theorem main :
    ∀ (A C : PowerSeries ℤ),
      PowerSeries.constantCoeff A = 1 →
      C = 1 + PowerSeries.X * C ^ 2 →
      (∀ n : ℕ, (∑ k ∈ Finset.range (n + 1), |PowerSeries.coeff k ((Ring.inverse A) ^ (n - k))|) =
        PowerSeries.coeff n C) →
      ∀ n : ℕ, 0 < n → (Odd (PowerSeries.coeff n A) ↔ ∃ k : ℕ, n = 2 ^ k) := by
  sorry

end OMA.S_oeis_a382122
