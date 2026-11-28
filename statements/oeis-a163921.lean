import Mathlib

namespace OMA.S_oeis_a163921

open PowerSeries BigOperators

/-- Coefficients of `exp(∑_{n ≥ 1} L(n) * x^n / n)` over `ℚ`, uniquely defined by
`a(0) = 1` and `n * a(n) = ∑_{j=1}^n L(j) * a(n - j)` for `n ≥ 1`. -/
def expLogCoeffs (L : ℕ → ℤ) : ℕ → ℚ
  | 0 => 1
  | n + 1 =>
      (∑ j : Fin (n + 1), (L (j.val + 1) : ℚ) * expLogCoeffs L (n - j.val)) / ((n + 1 : ℕ) : ℚ)
termination_by n => n
decreasing_by
  have := j.isLt
  omega

/-- The formal power series `exp(∑_{n ≥ 1} L(n) * x^n / n)` in `ℚ[[X]]`. -/
noncomputable def expLogSeries (L : ℕ → ℤ) : PowerSeries ℚ :=
  PowerSeries.mk (expLogCoeffs L)

/-- A formal power series in `ℚ[[X]]` is an integer series if every coefficient is an integer. -/
def isIntegerSeries (f : PowerSeries ℚ) : Prop :=
  ∀ n : ℕ, ∃ z : ℤ, PowerSeries.coeff n f = (z : ℚ)

/-- Formal power series substitution `f(c * X)`: `[X^k] f(c * X) = c^k * [X^k] f`. -/
noncomputable def scaleX (c : ℚ) (f : PowerSeries ℚ) : PowerSeries ℚ :=
  PowerSeries.mk fun k => c ^ k * PowerSeries.coeff k f

/-- Formal power series `∑_{n=1}^{N} (scaleX (L n) f)^n * X^n / n` truncated to terms `1 ≤ n ≤ N`,
which agrees with `∑_{n ≥ 1} f(L(n) * X)^n * X^n / n` through degree `N`. -/
noncomputable def logSeriesTrunc (L : ℕ → ℤ) (f : PowerSeries ℚ) (N : ℕ) : PowerSeries ℚ :=
  ∑ n ∈ Finset.Icc 1 N,
    PowerSeries.C ((1 : ℚ) / (n : ℚ)) * ((scaleX (L n : ℚ) f) ^ n * PowerSeries.X ^ n)

/-- Coefficients of the unique formal power series `G(x) = 1 + ∑_{n ≥ 1} g(n) x^n` satisfying
`G(x) = exp(∑_{n ≥ 1} G(L(n) * x)^n * x^n / n)`. -/
noncomputable def gCoeffs (L : ℕ → ℤ) : ℕ → ℚ
  | 0 => 1
  | n + 1 =>
      let Gprev : PowerSeries ℚ :=
        PowerSeries.mk fun j => if j < n + 1 then gCoeffs L j else 0
      let H : PowerSeries ℚ := logSeriesTrunc L Gprev (n + 1)
      (∑ k : Fin (n + 1),
        ((k.val + 1 : ℕ) : ℚ) * PowerSeries.coeff (k.val + 1) H * gCoeffs L (n - k.val)) /
        ((n + 1 : ℕ) : ℚ)
termination_by n => n
decreasing_by
  all_goals omega

/-- Conjecture on OEIS A163921 (Paul D. Hanna):
if `F(x) = exp(∑_{n ≥ 1} L(n) * x^n / n)` is an integer series, then
`G(x) = exp(∑_{n ≥ 1} G(L(n) * x)^n * x^n / n)` is also an integer series. -/
theorem main :
    ∀ L : ℕ → ℤ, isIntegerSeries (expLogSeries L) →
      ∀ n : ℕ, ∃ z : ℤ, gCoeffs L n = (z : ℚ) := by
  sorry

end OMA.S_oeis_a163921
