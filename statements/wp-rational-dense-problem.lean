import Mathlib

/-!
# Rational distances from the four corners of a unit square

Source: https://en.wikipedia.org/wiki/Unit_square#Rational_distance_problem
Credit: @dwilfand-sys
-/

namespace OMA.S_wp_rational_dense_problem

/-- The Euclidean distance from `(x, y)` to `(a, b)` is rational. -/
def HasRationalDistance (x y a b : ℝ) : Prop :=
  ∃ q : ℚ, Real.sqrt ((x - a) ^ 2 + (y - b) ^ 2) = (q : ℝ)

/-- Is there a point in the plane at rational distance from every vertex of the unit square? -/
theorem main :
    ∃ x y : ℝ, HasRationalDistance x y 0 0 ∧ HasRationalDistance x y 1 0 ∧
      HasRationalDistance x y 0 1 ∧ HasRationalDistance x y 1 1 := by
  sorry

end OMA.S_wp_rational_dense_problem
