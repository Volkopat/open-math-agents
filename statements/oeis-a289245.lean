import Mathlib.Analysis.Real.Sqrt
import Mathlib.Algebra.Order.Floor.Ring
import Mathlib.RingTheory.PowerSeries.Inverse

-- Formalization by Herman Palmgren (@PalmtreeBranch), using Codex.
-- Source: https://oeis.org/A289245

/-! Clark Kimberling's conjecture on the coefficients of the reciprocal series
in OEIS A289245 (July 2017). -/

namespace OMA.S_oeis_a289245

noncomputable def slope : ℝ := (3 + Real.sqrt 5) / 2

noncomputable def weight (n : ℕ) : ℤ := ⌊((n : ℝ) + 1) * slope⌋ - 1

/-- Start at index k in the weight sequence, with a positive first sign. -/
def alternatingSeries (u : ℕ → ℤ) (k : ℕ) : PowerSeries ℤ :=
  PowerSeries.mk fun j => (-1 : ℤ) ^ j * u (k + j)

/-- The inverse formed using the unit constant coefficient of the denominator. -/
noncomputable def generating : PowerSeries ℤ :=
  PowerSeries.invOfUnit (alternatingSeries weight 0) 1

noncomputable def a (n : ℕ) : ℤ := PowerSeries.coeff n generating

/-- The coefficients of the reciprocal power series are strictly increasing. -/
theorem main : StrictMono a := by
  sorry

end OMA.S_oeis_a289245
