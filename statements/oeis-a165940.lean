import Mathlib

namespace OMA.S_oeis_a165940

open PowerSeries BigOperators

/-- Coefficients of `exp(∑_{n ≥ 1} x^n / (n * 2^(n^2)))` over `ℚ`. -/
def a165940SeriesCoeffs : ℕ → ℚ
  | 0 => 1
  | n + 1 =>
      (∑ k : Fin (n + 1),
        ((1 : ℚ) / (2 : ℚ) ^ ((k.val + 1) ^ 2)) * a165940SeriesCoeffs (n - k.val)) / ((n + 1 : ℕ) : ℚ)
termination_by n => n
decreasing_by
  have := k.isLt
  omega

/-- OEIS A165940: `a(n) = 2^(n^2 + n) * [x^n] exp(∑_{k ≥ 1} x^k / (k * 2^(k^2)))`. -/
def a165940 (n : ℕ) : ℚ :=
  (2 : ℚ) ^ (n ^ 2 + n) * a165940SeriesCoeffs n

/-- Conjecture on OEIS A165940:
the sequence `a(n) = 2^(n^2 + n) * [x^n] exp(∑_{k ≥ 1} x^k / (k * 2^(k^2)))` consists entirely of integers. -/
theorem main :
    ∀ n : ℕ, ∃ z : ℤ, a165940 n = (z : ℚ) := by
  sorry

end OMA.S_oeis_a165940
