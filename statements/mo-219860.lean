import Mathlib

/-!
# A kaleidoscopic coloring of the Euclidean plane

Can the plane be partitioned into two Lebesgue measurable sets that each occupy
exactly half the area of every unit disk?

[MathOverflow question](https://mathoverflow.net/questions/219860/a-kaleidoscopic-coloring-of-the-plane)
-/

open MeasureTheory

namespace OMA.S_mo_219860

abbrev Plane := EuclideanSpace ℝ (Fin 2)

theorem main :
    ∃ A B : Set Plane,
      NullMeasurableSet A volume ∧ NullMeasurableSet B volume ∧
      Disjoint A B ∧ A ∪ B = Set.univ ∧
      ∀ center : Plane,
        let disk := Metric.closedBall center 1
        volume (A ∩ disk) = volume disk / 2 ∧
          volume (B ∩ disk) = volume disk / 2 := by
  sorry

end OMA.S_mo_219860
