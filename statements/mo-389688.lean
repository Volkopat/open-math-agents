import Mathlib

/-!
# Volume of a set vs volume of its projections

Source: https://mathoverflow.net/questions/389688
Credit: @artnoage

The source: let `V ⊂ ℝ^n` be nice (measurable or Borel or open or convex...), and let
`V_{i,j,...}` be the projection of `V` on the subspace spanned by `e_i, e_j, ...`. After
recalling `μ(V) ≤ ∏ μ(V_i)`, it asks about projections on higher dimensional subspaces, and
gives the precise instance: for `n = 3`, is it true that `μ(V)² ≤ μ(V_12) μ(V_13) μ(V_23)`?

Choices made here:

* The precise instance `n = 3` is stated. `ℝ³` is `ℝ × ℝ × ℝ` with its product Lebesgue
  measure, and the three coordinate planes are `ℝ × ℝ`.
* Of the regularity classes the source lists, the weakest one is used: `V` is measurable.
* The projections of a measurable set need not be measurable; `volume` of an arbitrary set is
  Lebesgue outer measure, which agrees with Lebesgue measure on the (analytic, hence Lebesgue
  measurable) projections of a Borel set.
-/

namespace OMA.S_mo_389688

open MeasureTheory

theorem main :
    ∀ V : Set (ℝ × ℝ × ℝ), MeasurableSet V →
      volume V ^ 2 ≤ volume ((fun p : ℝ × ℝ × ℝ => (p.1, p.2.1)) '' V) *
        volume ((fun p : ℝ × ℝ × ℝ => (p.1, p.2.2)) '' V) *
        volume ((fun p : ℝ × ℝ × ℝ => p.2) '' V) := by
  sorry

end OMA.S_mo_389688
