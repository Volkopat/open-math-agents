import Mathlib.RingTheory.PowerSeries.Basic
import Mathlib.RingTheory.PowerSeries.Inverse

namespace OMA.S_oeis_a397356

/-- Conjecture (OEIS A397356): If `A(x) = ∑ a(n) x^n ∈ ℤ[[x]]` satisfies `A(0) = 1`, `A'(0) = 1`,
and `[x^n] (1 / A(x))^(n^2) = [x^n] (1 / A(x))^(n^2 - 1)` for all `n > 1`, then for all `n ≥ 0`,
`a(n)` is odd if and only if `n + 1` is a power of `2`. -/
theorem main :
    ∀ A : PowerSeries ℤ,
      PowerSeries.constantCoeff A = 1 →
      PowerSeries.coeff 1 A = 1 →
      (∀ n : ℕ, 1 < n →
        PowerSeries.coeff n (Ring.inverse A ^ (n ^ 2)) =
          PowerSeries.coeff n (Ring.inverse A ^ (n ^ 2 - 1))) →
      ∀ n : ℕ, Odd (PowerSeries.coeff n A) ↔ ∃ k : ℕ, n + 1 = 2 ^ k := by
  sorry

end OMA.S_oeis_a397356
