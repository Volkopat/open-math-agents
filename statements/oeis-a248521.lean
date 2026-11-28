import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Data.Nat.Nth

/-!
# The indices of unit increases in the cotangent floor sequence

Only positive k occur in the source. The zero-based enumerator at index
j is the published term at index j+1. Since π/2 is positive, the stated
asymptotic a(n) ~ πn/2 is equivalently convergence of a(n)/n to π/2.

Source: https://oeis.org/A248521
Credit: @KoaOkano
-/

namespace OMA.S_oeis_a248521

noncomputable def height (k : ℕ) : ℤ := ⌊Real.cot (Real.pi/(2*(k:ℝ)))⌋

def selected (k : ℕ) : Prop := 0<k ∧ height (k+1) = height k+1

open Filter Topology

theorem main : Tendsto (fun j : ℕ => (Nat.nth selected j : ℝ) / ((j:ℝ)+1))
    atTop (𝓝 (Real.pi/2)) := by
  sorry

end OMA.S_oeis_a248521
