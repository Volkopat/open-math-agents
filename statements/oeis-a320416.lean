import Mathlib

namespace OMA.S_oeis_a320416

open PowerSeries BigOperators

/-- Sum of `k`-th powers of divisors of `n`: `σ_k(n) = ∑_{d ∣ n} d^k`. -/
def sigmaK (k n : ℕ) : ℕ :=
  ∑ d ∈ Nat.divisors n, d ^ k

/-- The rational sequence `L(n) = σ_2(n) * σ_3(n) / σ_1(n)` for `n ≥ 1`. -/
def L320416 (n : ℕ) : ℚ :=
  if n = 0 then 0 else ((sigmaK 2 n * sigmaK 3 n : ℕ) : ℚ) / (sigmaK 1 n : ℚ)

/-- Coefficients of `exp(∑_{n ≥ 1} (σ_2(n) * σ_3(n) / σ_1(n)) * x^n / n)` over `ℚ`,
uniquely defined by `a(0) = 1` and `n * a(n) = ∑_{j=1}^n L(j) * a(n - j)` for `n ≥ 1`. -/
def a320416 : ℕ → ℚ
  | 0 => 1
  | n + 1 =>
      (∑ j : Fin (n + 1), L320416 (j.val + 1) * a320416 (n - j.val)) / ((n + 1 : ℕ) : ℚ)
termination_by n => n
decreasing_by
  have := j.isLt
  omega

/-- Conjecture on OEIS A320416 (Paul D. Hanna):
the expansion of `exp(∑_{n ≥ 1} (σ_2(n) * σ_3(n) / σ_1(n)) * x^n / n)`
consists entirely of integers. -/
theorem main :
    ∀ n : ℕ, ∃ z : ℤ, a320416 n = (z : ℚ) := by
  sorry

end OMA.S_oeis_a320416
