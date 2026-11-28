import Mathlib

/-!
# The smooth slice–ribbon conjecture

Every knot in the three-sphere that bounds a smooth properly embedded disk in the
four-ball also bounds a ribbon disk there. A ribbon disk is in Morse position for
the radial height, with no interior local maxima.

[Open Problem Garden](https://www.openproblemgarden.org/op/slice_ribbon_problem_0)
[Radial Morse formulation](https://msp.org/gt/2010/14-4/gt-v14-n4-p13-s.pdf)
-/

open scoped ContDiff

namespace OMA.S_opg_slice_ribbon_problem_0

abbrev Euclidean (n : ℕ) := EuclideanSpace ℝ (Fin n)

abbrev UnitDisk := Metric.closedBall (0 : Euclidean 2) 1

abbrev BoundaryCircle := Metric.sphere (0 : Euclidean 2) 1

noncomputable def radialHeight (f : Euclidean 2 → Euclidean 4) (x : Euclidean 2) : ℝ :=
  ‖f x‖ ^ 2

def IsSliceDisk (f : Euclidean 2 → Euclidean 4) : Prop :=
  ContDiff ℝ ∞ f ∧ Set.InjOn f UnitDisk ∧
    ∀ x ∈ UnitDisk,
      Function.Injective (fderiv ℝ f x) ∧ ‖f x‖ ≤ 1 ∧
        (‖f x‖ = 1 ↔ x ∈ BoundaryCircle) ∧
        (x ∈ BoundaryCircle → fderiv ℝ (radialHeight f) x ≠ 0)

def IsRibbonPosition (f : Euclidean 2 → Euclidean 4) : Prop :=
  ∀ x ∈ Metric.ball (0 : Euclidean 2) 1,
    fderiv ℝ (radialHeight f) x = 0 →
      Function.Injective (fderiv ℝ (fderiv ℝ (radialHeight f)) x) ∧
        ¬ IsLocalMax (radialHeight f) x

theorem main :
    ∀ K : Set (Euclidean 4),
      (∃ f : Euclidean 2 → Euclidean 4,
        IsSliceDisk f ∧ f '' BoundaryCircle = K) →
      ∃ g : Euclidean 2 → Euclidean 4,
        IsSliceDisk g ∧ g '' BoundaryCircle = K ∧ IsRibbonPosition g := by
  sorry

end OMA.S_opg_slice_ribbon_problem_0
