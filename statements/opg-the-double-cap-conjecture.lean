import Mathlib

/-!
# The double cap conjecture

Source: https://www.openproblemgarden.org/op/the_double_cap_conjecture
Credit: @shc261392

Conjecture (Kalai): the largest measure of a Lebesgue measurable subset of the unit sphere of
`ℝⁿ` containing no pair of orthogonal vectors is attained by two open caps of geodesic radius
`π/4` around the north and south poles.

Reading used here:
* The space is `ℝ^(n+1)` (`EuclideanSpace ℝ (Fin (n+1))`, `n ≥ 0`), and the measure on the unit
  sphere is the surface measure `volume.toSphere`.
* The two open caps of geodesic radius `π/4` around the poles `± e₀` form the set of unit
  vectors `x` with `|x 0| > cos(π/4) = 1/√2`. This set itself contains no orthogonal pair, so
  the conjecture says every measurable orthogonal-pair-free set has measure at most its measure.
-/

namespace OMA.S_opg_the_double_cap_conjecture

open MeasureTheory

theorem main :
    ∀ (n : ℕ) (A : Set (Metric.sphere (0 : EuclideanSpace ℝ (Fin (n + 1))) 1)),
      MeasurableSet A →
      (∀ x ∈ A, ∀ y ∈ A, inner ℝ (x : EuclideanSpace ℝ (Fin (n + 1))) (y : EuclideanSpace ℝ
        (Fin (n + 1))) ≠ 0) →
        (volume : Measure (EuclideanSpace ℝ (Fin (n + 1)))).toSphere A ≤
          (volume : Measure (EuclideanSpace ℝ (Fin (n + 1)))).toSphere
            {x | 1 / Real.sqrt 2 < |(x : EuclideanSpace ℝ (Fin (n + 1))) 0|} := by
  sorry

end OMA.S_opg_the_double_cap_conjecture
