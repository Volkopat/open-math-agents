import Mathlib.NumberTheory.Real.Irrational
import Mathlib.Topology.MetricSpace.Sequences

/-! Source: https://mathoverflow.net/questions/237201 -/

namespace OMA.S_mo_237201

open Filter
open scoped Topology

noncomputable def scaledFract (ξ : ℝ) (n : ℕ) : ℝ :=
  2 * (n : ℝ) * Int.fract ((n : ℝ) * ξ) - (n : ℝ)

/-- The scaled fractional-part sequence has a finite cluster point
for every positive irrational ξ. -/
theorem main : ∀ ξ : ℝ, 0 < ξ → Irrational ξ →
    ∃ L : ℝ, ∃ s : ℕ → ℕ, StrictMono s ∧
      Tendsto (fun n => scaledFract ξ (s n)) atTop (𝓝 L) := by
  sorry

end OMA.S_mo_237201
