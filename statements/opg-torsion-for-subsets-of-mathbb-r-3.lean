import Mathlib

/-!
# Torsion for subsets of ℝ³

Source: https://www.openproblemgarden.org/op/torsion_for_subsets_of_mathbb_r_3
Credit: @lzvxck

The source: does there exist a subset of `ℝ³` such that its fundamental group has an element
of finite order? (The corresponding problem in `ℝ²` has a negative answer; in `ℝⁿ` for
`n ≥ 4` it has a positive answer.)

The existence (affirmative) form is stated. Conventions: an element of finite order means a
nontrivial element `g` with `g ^ n = 1` for some `n ≥ 1` (the identity trivially has finite
order). The subset `X ⊆ ℝ³` carries the subspace topology, and its fundamental group is taken
at some base point `x ∈ X` (Mathlib's `FundamentalGroup`).
-/

namespace OMA.S_opg_torsion_for_subsets_of_mathbb_r_3

/-- **Torsion for subsets of `ℝ³` (folklore).** Some subset of `ℝ³` has, at some base point, a
fundamental group with a nontrivial element of finite order. -/
theorem main : ∃ (X : Set (EuclideanSpace ℝ (Fin 3))) (x : X) (g : FundamentalGroup X x)
    (n : ℕ), 0 < n ∧ g ≠ 1 ∧ g ^ n = 1 := by
  sorry

end OMA.S_opg_torsion_for_subsets_of_mathbb_r_3
