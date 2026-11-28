import Mathlib

/-!
# Density of unit gaps in A389425

A199716 consists of the positive k for which both 6k−5 and 6k−1 are composite.
The enumeration below starts at index zero. Shifting the indices by one leaves
the natural density unchanged.

Source: https://oeis.org/A389425
Credit: @CubeJerry
-/

namespace OMA.S_oeis_a389425

open Filter Topology

def eligible (k : ℕ) : Prop :=
  1 < 6*k-5 ∧ ¬(6*k-5).Prime ∧ 1 < 6*k-1 ∧ ¬(6*k-1).Prime

noncomputable def term (i : ℕ) : ℕ := Nat.nth eligible i

noncomputable def units (N : ℕ) : ℕ := by
  classical
  exact ((Finset.range N).filter (fun i => term (i+1) - term i = 1)).card

theorem main : Tendsto (fun N : ℕ => (units N : ℝ) / N) atTop (𝓝 1) := by
  sorry

end OMA.S_oeis_a389425
