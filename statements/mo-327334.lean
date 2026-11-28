import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Analysis.SpecialFunctions.Log.Basic

/-! Source: https://mathoverflow.net/questions/327334 -/

namespace OMA.S_mo_327334

open Filter
open scoped Topology

noncomputable def finiteProduct (m J : ℕ) : ℝ :=
  ∏ j ∈ Finset.range J, Real.cos (2 * (m : ℝ) * Real.pi / (3 : ℝ) ^ (j + 1)) ^ 2

/-- The infinite product is the infimum of its decreasing finite truncations. -/
noncomputable def energy (k : ℕ) : ℝ :=
  ∑ m ∈ Finset.range (3 ^ k), ⨅ J : ℕ, finiteProduct m J

/-- The exponential growth rate for the Cantor Fourier energy sums. -/
theorem main :
    Tendsto (fun k : ℕ => Real.log (energy k) / (k : ℝ)) atTop
      (𝓝 (Real.log (3 / 2))) := by
  sorry

end OMA.S_mo_327334
