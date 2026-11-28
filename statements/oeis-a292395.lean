import Mathlib

namespace OMA.S_oeis_a292395

open PowerSeries BigOperators

/-- Conjecture on OEIS A292395 (Paul D. Hanna):
If `A(x) = ∑_{n ≥ 0} a(n) x^n ∈ ℚ[[X]]` with `a(0) = 1, a(1) = 1` and inverse `invA`
satisfies `[x^n] A(x / A(x)^(n^2)) = 0` for all `n > 1` (i.e., `A` is the g.f. of A292394),
then `A292395(n) = a(n) / n^2` is an integer for every `n ≥ 1`. -/
theorem main :
    ∀ A invA : PowerSeries ℚ,
      A * invA = 1 →
      PowerSeries.coeff 0 A = 1 →
      PowerSeries.coeff 1 A = 1 →
      (∀ n : ℕ, 2 ≤ n →
        PowerSeries.coeff n (∑ k ∈ Finset.range (n + 1),
          PowerSeries.C (PowerSeries.coeff k A) * (PowerSeries.X * invA ^ (n ^ 2)) ^ k) = 0) →
      ∀ n : ℕ, 1 ≤ n → ∃ z : ℤ, PowerSeries.coeff n A / ((n ^ 2 : ℕ) : ℚ) = (z : ℚ) := by
  sorry

end OMA.S_oeis_a292395
