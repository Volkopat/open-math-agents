import Mathlib

/-!
# The coefficient recurrence for OEIS A141344

Source: https://oeis.org/A141344 (Paul Barry).
R. J. Mathar conjectured the recurrence on 25 October 2012.

The square root is the formal binomial expansion with constant coefficient one.
The denominator has constant coefficient one as well. The index `k + 3` ranges
over exactly the indices for which all four terms of the recurrence are defined.
-/

namespace OMA.S_oeis_a141344

open PowerSeries

/-- The formal square root of `1 + 4X` with constant coefficient one. -/
noncomputable def rootSeries : PowerSeries ℚ :=
  rescale (4 : ℚ) (binomialSeries ℚ (1 / 2 : ℚ))

/-- The generating function `(2 - sqrt(1+4X)) / (2 - X - sqrt(1+4X))`. -/
noncomputable def generatingSeries : PowerSeries ℚ :=
  (2 - rootSeries) * (2 - X - rootSeries)⁻¹

noncomputable def a (n : ℕ) : ℚ := coeff n generatingSeries

theorem main : ∀ k : ℕ, let n : ℚ := (k : ℚ) + 3
    3 * (n - 1) * a (k + 3) + 2 * (2 * n - 11) * a (k + 2) +
    (79 - 31 * n) * a (k + 1) + 2 * (2 * n - 5) * a k = 0 := by
  sorry

end OMA.S_oeis_a141344
