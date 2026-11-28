import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecificLimits.Basic

/-!
# Kotesovec's normalized product limit (OEIS A366271)

Source: https://oeis.org/A366271 (Vaclav Kotesovec, October 6, 2023).
Credit: @NOELOO6

A is the limit of the defining geometric-mean product. In both products
i ranges from 0 to n−1, so the sampled points are exactly 1/n through 1.
-/

namespace OMA.S_oeis_a366271
open Filter Finset
open scoped Topology

noncomputable def g (x : ℝ) := x^x+(1-x)^x
noncomputable def point (n i : ℕ) : ℝ := ((i+1:ℕ):ℝ)/n

theorem main : ∃ A : ℝ, 0<A ∧
    Tendsto (fun n : ℕ => ∏ i ∈ range n, (g (point n i))^(1/(n:ℝ)))
      atTop (𝓝 A) ∧
    Tendsto (fun n : ℕ => (1/A^n)*∏ i ∈ range n, g (point n i))
      atTop (𝓝 (1/Real.sqrt 2)) := by
  sorry

end OMA.S_oeis_a366271
