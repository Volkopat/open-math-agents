import Mathlib

namespace OMA.S_oeis_a166168

open PowerSeries BigOperators

/-- Lucas numbers `L(n)` (OEIS A000204 for `n ≥ 1`): `L(0) = 2`, `L(1) = 1`, `L(n + 2) = L(n + 1) + L(n)`. -/
def lucas : ℕ → ℤ
  | 0 => 2
  | 1 => 1
  | n + 2 => lucas (n + 1) + lucas n

/-- Coefficients of `exp(∑_{n ≥ 1} Lucas(n^2) * x^n / n)` over `ℚ`,
uniquely defined by `a(0) = 1` and `n * a(n) = ∑_{k=1}^n Lucas(k^2) * a(n - k)` for `n ≥ 1`. -/
def a166168Coeffs : ℕ → ℚ
  | 0 => 1
  | n + 1 =>
      (∑ k : Fin (n + 1), (lucas ((k.val + 1) ^ 2) : ℚ) * a166168Coeffs (n - k.val)) / ((n + 1 : ℕ) : ℚ)
termination_by n => n
decreasing_by
  have := k.isLt
  omega

/-- Conjecture on OEIS A166168:
the power series `exp(∑_{n ≥ 1} Lucas(n^2) * x^n / n)` consists entirely of integers. -/
theorem main :
    ∀ n : ℕ, ∃ z : ℤ, a166168Coeffs n = (z : ℚ) := by
  sorry

end OMA.S_oeis_a166168
