import Mathlib

namespace OMA.S_oeis_a207969

open PowerSeries BigOperators

/-- Coefficients of `exp(∑_{n ≥ 1} 5 * Fibonacci(n)^(2*k) * x^n / n)` over `ℚ`,
uniquely defined by `a(0) = 1` and `n * a(n) = ∑_{j=1}^n 5 * Fibonacci(j)^(2*k) * a(n - j)` for `n ≥ 1`. -/
def fibPowExpCoeffs (k : ℕ) : ℕ → ℚ
  | 0 => 1
  | n + 1 =>
      (∑ j : Fin (n + 1),
        (5 * (Nat.fib (j.val + 1) : ℚ) ^ (2 * k)) * fibPowExpCoeffs k (n - j.val)) / ((n + 1 : ℕ) : ℚ)
termination_by n => n
decreasing_by
  have := j.isLt
  omega

/-- Conjecture on OEIS A207969:
`exp(∑_{n ≥ 1} 5 * Fibonacci(n)^(2*k) * x^n / n)` is an integer power series for all integers `k ≥ 0`. -/
theorem main :
    ∀ k n : ℕ, ∃ z : ℤ, fibPowExpCoeffs k n = (z : ℚ) := by
  sorry

end OMA.S_oeis_a207969
