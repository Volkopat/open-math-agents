import Mathlib

namespace OMA.S_oeis_a129509

open PowerSeries BigOperators

/-- The polynomial `g(n, X) = ∑_{k=0}^n C(n, k)^2 * X^k` in `ℚ[[X]]`. -/
noncomputable def gPoly (n : ℕ) : PowerSeries ℚ :=
  ∑ k ∈ Finset.range (n + 1),
    PowerSeries.C ((Nat.choose n k : ℚ) ^ 2) * PowerSeries.X ^ k

/-- Truncated logarithm series `L_N(X) = ∑_{n=1}^N g(n, X) * (-X)^n / n`,
which agrees with `∑_{n ≥ 1} g(n, X) * (-X)^n / n` through degree `N`. -/
noncomputable def balaLogTrunc (N : ℕ) : PowerSeries ℚ :=
  ∑ n ∈ Finset.Icc 1 N,
    PowerSeries.C ((1 : ℚ) / (n : ℚ)) * (gPoly n * (-PowerSeries.X) ^ n)

/-- The formal power series `L(X) = ∑_{n ≥ 1} g(n, X) * (-X)^n / n` in `ℚ[[X]]`. -/
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

/-- The exponential formal power series `exp(∑_{n ≥ 1} g(n, X) * (-X)^n / n)` in `ℚ[[X]]`. -/
noncomputable def balaExp : PowerSeries ℚ :=
  PowerSeries.mk (expCoeffs balaLog)

/-- Conjectures on OEIS A129509 (Joerg Arndt & Peter Bala):
Let `A(x) = (1 + x + x^2 - sqrt(1 + 2x + 3x^2 - 2x^3 + x^4)) / 2`, uniquely characterized
as the formal power series with `A(0) = 0` satisfying `A(x)^2 - (1 + x + x^2) A(x) + x^3 = 0`.
Then:
1. For the continued-fraction series `G(x)` with `G(0) = 1` satisfying `G = 1 + x / (1 + x^2 / G)`
   (equivalently `G * (G + x^2) = G + x^2 + x * G`), we have `G * (x^2 - A) = x^2`
   (i.e. `A(x) = x^2 * (1 - 1 / G(x))`);
2. `A(x) = x^3 * exp(∑_{n ≥ 1} g(n, x) * (-x)^n / n)` where `g(n, x) = ∑_{k=0}^n C(n, k)^2 x^k`. -/
theorem main :
    ∀ A : PowerSeries ℚ,
      PowerSeries.coeff 0 A = 0 →
      A ^ 2 - (1 + PowerSeries.X + PowerSeries.X ^ 2) * A + PowerSeries.X ^ 3 = 0 →
      (∀ G : PowerSeries ℚ,
        PowerSeries.coeff 0 G = 1 →
        G * (G + PowerSeries.X ^ 2) = G + PowerSeries.X ^ 2 + PowerSeries.X * G →
        G * (PowerSeries.X ^ 2 - A) = PowerSeries.X ^ 2) ∧
      A = PowerSeries.X ^ 3 * balaExp := by
  sorry

end OMA.S_oeis_a129509
