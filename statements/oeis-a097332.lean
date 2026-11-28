import Mathlib

/-!
# The recurrence for the coefficients of OEIS A097332

Source: https://oeis.org/A097332 (Paul Barry).
R. J. Mathar conjectured the recurrence on 26 November 2012.

The polynomial under the square root factors as (1 + X)(1 - 3X).
The binomial series for the two square roots both have constant coefficient one.
-/

namespace OMA.S_oeis_a097332

open PowerSeries

/-- The constant-one square root of `1 - 2X - 3X²`. -/
noncomputable def rootSeries : PowerSeries ℚ :=
  PowerSeries.binomialSeries ℚ (1 / 2 : ℚ) *
    rescale (-3 : ℚ) (PowerSeries.binomialSeries ℚ (1 / 2 : ℚ))

/-- The generating function `(1-X)⁻¹ (1 + 2X/(1-X+sqrt(1-2X-3X²)))`. -/
noncomputable def generatingSeries : PowerSeries ℚ :=
  (1 - X)⁻¹ * (1 + 2 * X * (1 - X + rootSeries)⁻¹)

noncomputable def a (n : ℕ) : ℚ := coeff n generatingSeries

theorem main : ∀ k : ℕ, let n : ℚ := (k : ℚ) + 3
    (n + 1) * a (k + 3) - 3 * n * a (k + 2) +
    (-n + 5) * a (k + 1) + 3 * (n - 2) * a k = 0 := by
  sorry

end OMA.S_oeis_a097332
