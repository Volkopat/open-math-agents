import Mathlib

namespace OMA.S_oeis_a384819

open PowerSeries BigOperators

/-- Exponential power series `A(x) = exp(∑_{n ≥ 1} C(n) * x^n / n)` over `ℚ`,
uniquely defined by `a(0) = 1` and `n * a(n) = ∑_{k=1}^n C(k) * a(n - k)` for `n ≥ 1`. -/
def expLogCoeffs (C : ℕ → ℤ) : ℕ → ℚ
  | 0 => 1
  | n + 1 =>
      (∑ k : Fin (n + 1), (C (k.val + 1) : ℚ) * expLogCoeffs C (n - k.val)) / ((n + 1 : ℕ) : ℚ)
termination_by n => n
decreasing_by
  have := k.isLt
  omega

/-- The formal power series `exp(∑_{n ≥ 1} C(n) * x^n / n)` over `ℚ`. -/
noncomputable def expLogSeries (C : ℕ → ℤ) : PowerSeries ℚ :=
  PowerSeries.mk (expLogCoeffs C)

/-- Predicate that a formal power series over `ℚ` has integer coefficients. -/
def isIntegerSeries (f : PowerSeries ℚ) : Prop :=
  ∀ n : ℕ, ∃ z : ℤ, PowerSeries.coeff n f = (z : ℚ)

/-- OEIS A384819 conjecture:
"Nonnegative numbers a(n) < n for n >= 1 such that exp( Sum_{n>=1} (n^2 - a(n))*x^n/n )
is a power series with integral coefficients.
Conjecture: a(p^n) = p - 1 when p is prime for n >= 1." -/
theorem main :
    ∀ a : ℕ → ℕ,
      (∀ n : ℕ, 1 ≤ n → a n < n) →
      isIntegerSeries (expLogSeries fun n => (n : ℤ) ^ 2 - (a n : ℤ)) →
      ∀ p n : ℕ, p.Prime → 1 ≤ n → a (p ^ n) = p - 1 := by sorry

end OMA.S_oeis_a384819
