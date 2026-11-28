import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Data.Nat.Nth

/-!
# The indices of repeated values in the cotangent floor sequence

The source takes positive k and numbers its selected indices from one.
The zero-based enumerator at j therefore gives the source term at j+1.
The limit stated here is equivalent to a(n) ~ πn/(π−2).

Source: https://oeis.org/A248520
Credit: @KoaOkano
-/

namespace OMA.S_oeis_a248520

noncomputable def height (k : ℕ) : ℤ := ⌊Real.cot (Real.pi/(2*(k:ℝ)))⌋

def selected (k : ℕ) : Prop := 0<k ∧ height (k+1) = height k

open Filter Topology

theorem main : Tendsto (fun j : ℕ => (Nat.nth selected j : ℝ) / ((j:ℝ)+1))
    atTop (𝓝 (Real.pi/(Real.pi-2))) := by
  sorry

end OMA.S_oeis_a248520
