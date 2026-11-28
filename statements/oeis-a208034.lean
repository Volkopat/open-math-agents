import Mathlib

namespace OMA.S_oeis_a208034

open PowerSeries BigOperators

/-- Pell numbers `A000129`: `pell 0 = 0`, `pell 1 = 1`, `pell (n + 2) = 2 * pell (n + 1) + pell n`. -/
def pell : ℕ → ℕ
  | 0 => 0
  | 1 => 1
  | n + 2 => 2 * pell (n + 1) + pell n

/-- Coefficients of `exp(∑_{n ≥ 1} C(n) * x^n / n)` over `ℚ`, uniquely defined by
`a(0) = 1` and `n * a(n) = ∑_{j=1}^n C(j) * a(n - j)` for `n ≥ 1`. -/
def expLogCoeffs (C : ℕ → ℤ) : ℕ → ℚ
  | 0 => 1
  | n + 1 =>
      (∑ j : Fin (n + 1), (C (j.val + 1) : ℚ) * expLogCoeffs C (n - j.val)) / ((n + 1 : ℕ) : ℚ)
termination_by n => n
decreasing_by
  have := j.isLt
  omega

/-- The formal power series `exp(∑_{n ≥ 1} C(n) * x^n / n)` in `ℚ[[X]]`. -/
noncomputable def expLogSeries (C : ℕ → ℤ) : PowerSeries ℚ :=
  PowerSeries.mk (expLogCoeffs C)

/-- A formal power series in `ℚ[[X]]` is an integer series if every coefficient is an integer. -/
def isIntegerSeries (f : PowerSeries ℚ) : Prop :=
  ∀ n : ℕ, ∃ z : ℤ, PowerSeries.coeff n f = (z : ℚ)

/-- Conjectures on OEIS A208034 (Paul D. Hanna):
For all positive integers `k ≥ 1`:
(1) `exp(∑_{n ≥ 1} 2 * Pell(n)^(2*k) * x^n / n)` is an integer series;
(2) `exp(∑_{n ≥ 1} 2 * Pell(n)^(2*k - 1) * x^n / n)` is NOT an integer series;
(3) `exp(∑_{n ≥ 1} Pell(n)^(2*k) * x^n / n)` is NOT an integer series. -/
theorem main :
    ∀ k : ℕ, 1 ≤ k →
      isIntegerSeries (expLogSeries fun n => 2 * (pell n : ℤ) ^ (2 * k)) ∧
      ¬ isIntegerSeries (expLogSeries fun n => 2 * (pell n : ℤ) ^ (2 * k - 1)) ∧
      ¬ isIntegerSeries (expLogSeries fun n => (pell n : ℤ) ^ (2 * k)) := by
  sorry

end OMA.S_oeis_a208034
