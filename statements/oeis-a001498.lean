import Mathlib

/-!
# A001498: Generating function continued fraction for coefficients of Bessel polynomials

Source: https://oeis.org/A001498
-- Credit: @Dugongue (agent: Claude Code, model claude-opus-5-5)
Draft from an earlier generic agent run; audited against the source and re-checked before submission.

Conjecture: Let `a(n, k) = (n + k)! / ((n - k)! * k! * 2^k)` (`n ≥ 0, 0 ≤ k ≤ n`) be the
triangle of coefficients of the Bessel polynomials `y_n(x)`, and let
`G(x, y) = ∑_{n ≥ 0} ∑_{k = 0}^n a(n, k) x^n y^k`. Then `G(x, y) = T(0) / (1 - x)`,
where `T(k)` satisfies the continued fraction recurrence
`T(k) = 1 - x*y*(k+1) / (x*y*(k+1) - (1-x)^2 / T(k+1))`,
equivalently `T(k) * ((1 - x)^2 - (k + 1) * x * y * T(k + 1)) = (1 - x)^2`.

Conventions:
- Formal power series in two variables `(x, y)` over `ℚ` are represented as
  `PowerSeries (PowerSeries ℚ)`, where `x = PowerSeries.C PowerSeries.X` and
  `y = PowerSeries.X`.
-/

namespace OMA.S_oeis_a001498

/-- Coefficient `a(n, k)` of `x^k` in the Bessel polynomial `y_n(x)`. -/
def besselCoeff (n k : ℕ) : ℚ :=
  if k ≤ n then
    ((Nat.factorial (n + k) : ℚ) /
      ((Nat.factorial (n - k) : ℚ) * (Nat.factorial k : ℚ) * (2 : ℚ) ^ k))
  else 0

/-- Bivariate generating function `∑_{k ≥ 0} (∑_{n ≥ 0} a(n, k) x^n) y^k`. -/
noncomputable def besselGF : PowerSeries (PowerSeries ℚ) :=
  PowerSeries.mk fun k => PowerSeries.mk fun n => besselCoeff n k

theorem main :
    ∃ T : ℕ → PowerSeries (PowerSeries ℚ),
      (∀ k : ℕ,
        T k * ((1 - PowerSeries.C PowerSeries.X) ^ 2 -
          ((k + 1 : ℕ) : PowerSeries (PowerSeries ℚ)) *
            PowerSeries.C PowerSeries.X * PowerSeries.X * T (k + 1)) =
          (1 - PowerSeries.C PowerSeries.X) ^ 2) ∧
      (1 - PowerSeries.C PowerSeries.X) * besselGF = T 0 := by
  sorry

end OMA.S_oeis_a001498
