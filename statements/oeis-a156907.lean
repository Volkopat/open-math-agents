import Mathlib

namespace OMA.S_oeis_a156907

open PowerSeries BigOperators

/-- Formal power series substitution `f(c * X)`: `[X^k] f(c * X) = c^k * [X^k] f`. -/
noncomputable def scaleX (c : ℚ) (f : PowerSeries ℚ) : PowerSeries ℚ :=
  PowerSeries.mk fun k => c ^ k * PowerSeries.coeff k f

/-- Truncated log series `∑_{k=1}^{N} (scaleX (2^k) f - 1)^k / k`, which for `f(0) = 1`
agrees with `∑_{k ≥ 1} (f(2^k * X) - 1)^k / k` through degree `N`. -/
noncomputable def logSeriesTrunc (f : PowerSeries ℚ) (N : ℕ) : PowerSeries ℚ :=
  ∑ k ∈ Finset.Icc 1 N,
    PowerSeries.C ((1 : ℚ) / (k : ℚ)) * (scaleX ((2 : ℚ) ^ k) f - 1) ^ k

/-- Coefficients of `B(x) = (A(x) - 1) / x = exp(∑_{k ≥ 1} (A(2^k * x) - 1)^k / k)` where
`A(x) = 1 + x * B(x)` is OEIS A156907. -/
noncomputable def b156907 : ℕ → ℚ
  | 0 => 1
  | n + 1 =>
      let Aprev : PowerSeries ℚ :=
        PowerSeries.mk fun j =>
          if j = 0 then 1
          else if j < n + 2 then b156907 (j - 1) else 0
      let G : PowerSeries ℚ := logSeriesTrunc Aprev (n + 1)
      (∑ k : Fin (n + 1),
        ((k.val + 1 : ℕ) : ℚ) * PowerSeries.coeff (k.val + 1) G * b156907 (n - k.val)) /
        ((n + 1 : ℕ) : ℚ)
termination_by n => n
decreasing_by
  all_goals omega

/-- OEIS A156907: `A(x) = 1 + x * exp(∑_{k ≥ 1} (A(2^k * x) - 1)^k / k)`. -/
noncomputable def a156907 : ℕ → ℚ
  | 0 => 1
  | n + 1 => b156907 n

/-- Conjecture on OEIS A156907:
the sequence `A(x) = 1 + x * exp(∑_{k ≥ 1} (A(2^k * x) - 1)^k / k)` consists entirely of integers. -/
theorem main :
    ∀ n : ℕ, ∃ z : ℤ, a156907 n = (z : ℚ) := by
  sorry

end OMA.S_oeis_a156907
