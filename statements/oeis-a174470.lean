import Mathlib

namespace OMA.S_oeis_a174470

open PowerSeries BigOperators

/-- OEIS A014578 (binary expansion of Thue/Roth constant):
`a014578 n = 1` if `n ≥ 1` and the `3`-adic valuation `n.factorization 3` is even, else `0`. -/
def a014578 (n : ℕ) : ℤ :=
  if n = 0 then 0 else if Even (n.factorization 3) then 1 else 0

/-- Coefficients of `exp(∑_{n ≥ 1} A014578(n) * (3 * x)^n / n)` over `ℚ`. -/
def a174470Coeffs : ℕ → ℚ
  | 0 => 1
  | n + 1 =>
      (∑ k : Fin (n + 1),
        ((a014578 (k.val + 1) * (3 : ℤ) ^ (k.val + 1) : ℤ) : ℚ) * a174470Coeffs (n - k.val)) /
        ((n + 1 : ℕ) : ℚ)
termination_by n => n
decreasing_by
  have := k.isLt
  omega

/-- Conjecture on OEIS A174470:
the power series `exp(∑_{n ≥ 1} A014578(n) * (3 * x)^n / n)` consists entirely of integers. -/
theorem main :
    ∀ n : ℕ, ∃ z : ℤ, a174470Coeffs n = (z : ℚ) := by
  sorry

end OMA.S_oeis_a174470
