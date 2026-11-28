import Mathlib.Analysis.Real.Sqrt
import Mathlib.Algebra.Order.Floor.Ring
import Mathlib.RingTheory.PowerSeries.Inverse

-- Formalization by Herman Palmgren (@PalmtreeBranch), using Codex.
-- Source: https://oeis.org/A281112 and https://oeis.org/A078140

/-! Clark Kimberling conjectured that the ratios of successive coefficients of
A078140 converge. A281112 records the first 86 digits, including the integer
part. The bounds below specify every digit in the published table. -/

namespace OMA.S_oeis_a281112
open Filter Topology PowerSeries

noncomputable def weight (n : ℕ) : ℝ :=
  (⌊((n : ℝ) + 1) * ((1 + Real.sqrt 5) / 2)⌋ : ℤ)

noncomputable def denominator : PowerSeries ℝ :=
  PowerSeries.mk fun n => weight n * (-1)^n

noncomputable def a (n : ℕ) : ℝ := coeff n denominator⁻¹

def digits : ℕ :=
  16889241107691652066863596437198336089614626466166721916456635666408929438604845975694

theorem main : ∃ L : ℝ, Tendsto (fun n : ℕ => a (n+1) / a n) atTop (𝓝 L) ∧
    (digits : ℝ) / 10^85 ≤ L ∧ L < ((digits : ℝ) + 1) / 10^85 := by
  sorry

end OMA.S_oeis_a281112
