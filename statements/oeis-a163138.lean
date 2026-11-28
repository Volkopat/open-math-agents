import Mathlib

namespace OMA.S_oeis_a163138

open PowerSeries BigOperators

/-- Truncated log series `∑_{n=1}^{N} (q^n + f)^n * X^n / n`, which agrees with
`∑_{n ≥ 1} (q^n + f)^n * X^n / n` through degree `N`. -/
noncomputable def logSeriesTrunc (q : ℤ) (f : PowerSeries ℚ) (N : ℕ) : PowerSeries ℚ :=
  ∑ n ∈ Finset.Icc 1 N,
    PowerSeries.C ((1 : ℚ) / (n : ℚ)) * ((PowerSeries.C ((q : ℚ) ^ n) + f) ^ n * PowerSeries.X ^ n)

/-- Coefficients of the unique formal power series `A(x, q) = 1 + ∑_{n ≥ 1} a(n, q) x^n`
satisfying `A(x, q) = exp(∑_{n ≥ 1} (q^n + A(x, q))^n * x^n / n)`. -/
noncomputable def a163138 (q : ℤ) : ℕ → ℚ
  | 0 => 1
  | n + 1 =>
      let Aprev : PowerSeries ℚ :=
        PowerSeries.mk fun j => if j < n + 1 then a163138 q j else 0
      let G : PowerSeries ℚ := logSeriesTrunc q Aprev (n + 1)
      (∑ k : Fin (n + 1),
        ((k.val + 1 : ℕ) : ℚ) * PowerSeries.coeff (k.val + 1) G * a163138 q (n - k.val)) /
        ((n + 1 : ℕ) : ℚ)
termination_by n => n
decreasing_by
  all_goals omega

/-- Conjecture on OEIS A163138:
for every integer `q`, the formal power series `A(x, q) = exp(∑_{n ≥ 1} (q^n + A(x, q))^n * x^n / n)`
has integer coefficients. -/
theorem main :
    ∀ (q : ℤ) (n : ℕ), ∃ z : ℤ, a163138 q n = (z : ℚ) := by
  sorry

end OMA.S_oeis_a163138
