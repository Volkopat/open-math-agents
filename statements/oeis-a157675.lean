import Mathlib

namespace OMA.S_oeis_a157675

open PowerSeries BigOperators

/-- Formal power series substitution `f(c * X)`: `[X^k] f(c * X) = c^k * [X^k] f`. -/
noncomputable def scaleX (c : ℚ) (f : PowerSeries ℚ) : PowerSeries ℚ :=
  PowerSeries.mk fun k => c ^ k * PowerSeries.coeff k f

/-- Formal power series `∑_{n=1}^{N} (scaleX (2^n) f)^n * X^n / n` truncated to terms `1 ≤ n ≤ N`,
which agrees with `∑_{n ≥ 1} f(2^n * X)^n * X^n / n` through degree `N`. -/
noncomputable def logSeriesTrunc (f : PowerSeries ℚ) (N : ℕ) : PowerSeries ℚ :=
  ∑ n ∈ Finset.Icc 1 N,
    PowerSeries.C ((1 : ℚ) / (n : ℚ)) * ((scaleX ((2 : ℚ) ^ n) f) ^ n * PowerSeries.X ^ n)

/-- Coefficients of the unique formal power series `A(x) = 1 + ∑_{n ≥ 1} a(n) x^n` satisfying
`A(x) = exp(∑_{n ≥ 1} A(2^n * x)^n * x^n / n)`, i.e.
`X * A'(x) = A(x) * X * (∑_{n ≥ 1} A(2^n * x)^n * x^n / n)'`. -/
noncomputable def a157675 : ℕ → ℚ
  | 0 => 1
  | n + 1 =>
      let Aprev : PowerSeries ℚ :=
        PowerSeries.mk fun j => if j < n + 1 then a157675 j else 0
      let G : PowerSeries ℚ := logSeriesTrunc Aprev (n + 1)
      (∑ k : Fin (n + 1),
        ((k.val + 1 : ℕ) : ℚ) * PowerSeries.coeff (k.val + 1) G * a157675 (n - k.val)) /
        ((n + 1 : ℕ) : ℚ)
termination_by n => n
decreasing_by
  all_goals omega

/-- Conjecture on OEIS A157675:
the unique formal power series `A(x) = exp(∑_{n ≥ 1} A(2^n * x)^n * x^n / n)`
consists entirely of integer coefficients. -/
theorem main :
    ∀ n : ℕ, ∃ z : ℤ, a157675 n = (z : ℚ) := by
  sorry

end OMA.S_oeis_a157675
