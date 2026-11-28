import Mathlib

namespace OMA.S_oeis_a181316

open PowerSeries BigOperators

/-- The integer `((q^n - 1) / (q - 1)) = ∑_{i=0}^{n-1} q^i`. -/
def repunit (q : ℤ) (n : ℕ) : ℤ :=
  ∑ i ∈ Finset.range n, q ^ i

/-- Coefficients of `exp(∑_{n ≥ 1} (q - 1) * ((q^n - 1) / (q - 1))^(n - 1) * x^n / n)` over `ℚ`. -/
def a181316Coeffs (q : ℤ) : ℕ → ℚ
  | 0 => 1
  | n + 1 =>
      (∑ j : Fin (n + 1),
        (((q - 1) * (repunit q (j.val + 1)) ^ j.val : ℤ) : ℚ) * a181316Coeffs q (n - j.val)) /
        ((n + 1 : ℕ) : ℚ)
termination_by n => n
decreasing_by
  have := j.isLt
  omega

/-- Conjecture on OEIS A181316:
`exp(∑_{n ≥ 1} (q - 1) * ((q^n - 1) / (q - 1))^(n - 1) * x^n / n)` is an integer power series
for all integers `q > 1`. -/
theorem main :
    ∀ q : ℤ, 1 < q → ∀ n : ℕ, ∃ z : ℤ, a181316Coeffs q n = (z : ℚ) := by
  sorry

end OMA.S_oeis_a181316
