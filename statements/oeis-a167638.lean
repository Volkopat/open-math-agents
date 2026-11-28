import Mathlib

namespace OMA.S_oeis_a167638

open PowerSeries BigOperators

/-- The Legendre-like polynomial `g(n, X) = ∑_{k=0}^n C(n, k)^2 * (1 + X)^k` in `ℚ[[X]]`. -/
noncomputable def gPoly (n : ℕ) : PowerSeries ℚ :=
  ∑ k ∈ Finset.range (n + 1),
    PowerSeries.C ((Nat.choose n k : ℚ) ^ 2) * (1 + PowerSeries.X) ^ k

/-- Truncated logarithm series `L_N(X) = ∑_{n=1}^N g(n, X) * X^(2*n) / n`,
which agrees with `∑_{n ≥ 1} g(n, X) * X^(2*n) / n` through degree `2 * N`. -/
noncomputable def balaLogTrunc (N : ℕ) : PowerSeries ℚ :=
  ∑ n ∈ Finset.Icc 1 N,
    PowerSeries.C ((1 : ℚ) / (n : ℚ)) * (gPoly n * PowerSeries.X ^ (2 * n))

/-- The formal power series `L(X) = ∑_{n ≥ 1} g(n, X) * X^(2*n) / n` in `ℚ[[X]]`. -/
noncomputable def balaLog : PowerSeries ℚ :=
  PowerSeries.mk fun m => PowerSeries.coeff m (balaLogTrunc m)

/-- Coefficients of `exp(L)` for a formal power series `L` with zero constant term,
uniquely defined by `a(0) = 1` and `n * a(n) = ∑_{k=1}^n k * [X^k] L * a(n - k)`. -/
noncomputable def expCoeffs (L : PowerSeries ℚ) : ℕ → ℚ
  | 0 => 1
  | n + 1 =>
      (∑ k : Fin (n + 1),
        ((k.val + 1 : ℕ) : ℚ) * PowerSeries.coeff (k.val + 1) L * expCoeffs L (n - k.val)) /
        ((n + 1 : ℕ) : ℚ)
termination_by n => n
decreasing_by
  have := k.isLt
  omega

/-- The exponential formal power series `exp(∑_{n ≥ 1} g(n, X) * X^(2*n) / n)` in `ℚ[[X]]`. -/
noncomputable def balaExp : PowerSeries ℚ :=
  PowerSeries.mk (expCoeffs balaLog)

/-- Conjecture on OEIS A167638 (Peter Bala, Sep 10 2024):
The generating function `A(x) = (1 + 2x - x^3 - sqrt(1 - 4x^2 - 2x^3 + x^6)) / (2x(1+x))`
of A167638 — uniquely characterized as the formal power series with `A(0) = 1` satisfying
`x(1 + x) A(x)^2 - (1 + 2x - x^3) A(x) + (1 + x - x^2) = 0` — equals
`1 + x^3 * exp(∑_{n ≥ 1} g(n, x) * x^(2*n) / n)` where `g(n, x) = ∑_{k=0}^n C(n, k)^2 (1 + x)^k`. -/
theorem main :
    ∀ A : PowerSeries ℚ,
      PowerSeries.coeff 0 A = 1 →
      PowerSeries.X * (1 + PowerSeries.X) * A ^ 2 -
        (1 + PowerSeries.C 2 * PowerSeries.X - PowerSeries.X ^ 3) * A +
        (1 + PowerSeries.X - PowerSeries.X ^ 2) = 0 →
      A = 1 + PowerSeries.X ^ 3 * balaExp := by
  sorry

end OMA.S_oeis_a167638
