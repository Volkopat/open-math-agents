import Mathlib

namespace OMA.S_oeis_a353050

open PowerSeries BigOperators

/-- Exponential power series `A(x) = exp(∑_{n ≥ 1} L(n) * x^n / n)` over `ℚ`,
uniquely defined by `a(0) = 1` and `n * a(n) = ∑_{k=1}^n L(k) * a(n - k)` for `n ≥ 1`. -/
def expLogCoeffs (L : ℕ → ℤ) : ℕ → ℚ
  | 0 => 1
  | n + 1 =>
      (∑ k : Fin (n + 1), (L (k.val + 1) : ℚ) * expLogCoeffs L (n - k.val)) / ((n + 1 : ℕ) : ℚ)
termination_by n => n
decreasing_by
  have := k.isLt
  omega

/-- The formal power series `exp(∑_{n ≥ 1} L(n) * x^n / n)` over `ℚ`. -/
noncomputable def expLogSeries (L : ℕ → ℤ) : PowerSeries ℚ :=
  PowerSeries.mk (expLogCoeffs L)

/-- Predicate that a formal power series over `ℚ` has integer coefficients. -/
def isIntegerSeries (f : PowerSeries ℚ) : Prop :=
  ∀ n : ℕ, ∃ z : ℤ, PowerSeries.coeff n f = (z : ℚ)

/-- The truncated series `∑_{n=1}^{N} (L(n) - F(x))^n * x^n / n` for a power series `F` over `ℚ`. -/
noncomputable def implicitLogTrunc (L : ℕ → ℤ) (F : PowerSeries ℚ) (N : ℕ) : PowerSeries ℚ :=
  ∑ n ∈ Finset.Icc 1 N,
    PowerSeries.C ((1 : ℚ) / (n : ℚ)) *
      ((PowerSeries.C (L n : ℚ) - F) ^ n * PowerSeries.X ^ n)

/-- OEIS A353050 (general conjecture, which includes the Lucas-number case as a special case):
"G.f. A(x) satisfies: 0 = Sum_{n>=1} (Lucas(n) - A(x))^n * x^n/n, where Lucas(n) = A000204(n).
It is conjectured that this is an integer sequence. This sequence is a special case of a more
general conjecture: 0 = Sum_{n>=1} (L(n) - F(x))^n * x^n/n is satisfied by an integer series F(x)
if exp( Sum_{n>=1} L(n) * x^n/n ) yields an integer series." -/
theorem main :
    ∀ (L : ℕ → ℤ) (F : PowerSeries ℚ),
      isIntegerSeries (expLogSeries L) →
      (∀ k : ℕ, 1 ≤ k → PowerSeries.coeff k (implicitLogTrunc L F k) = 0) →
      isIntegerSeries F := by sorry

end OMA.S_oeis_a353050
