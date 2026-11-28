import Mathlib

namespace OMA.S_mo_109583

universe u

abbrev MeasurableSets {X : Type u} (m : MeasurableSpace X) :=
  {s : Set X // @MeasurableSet X m s}

/-- Is each concrete sigma algebra isomorphic to the Borel sigma algebra
of some topological space? -/
theorem main :
    ∀ (X : Type u) (m : MeasurableSpace X),
      ∃ (Y : Type u) (t : TopologicalSpace Y),
        Nonempty (MeasurableSets m ≃o MeasurableSets (@borel Y t)) := by
  sorry

end OMA.S_mo_109583
