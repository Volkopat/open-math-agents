import Mathlib

namespace OMA.S_mo_258842

def rectangles : Set (Set (ℝ × ℝ)) :=
  {S | ∃ A B : Set ℝ, S = A ×ˢ B}

def AllSetsGeneratedByRectangles : Prop :=
  ∀ S : Set (ℝ × ℝ), @MeasurableSet _ (MeasurableSpace.generateFrom rectangles) S

def AllContinuumFamiliesCountablyGenerated : Prop :=
  ∀ F : Set (Set ℝ), Nonempty (↥F ≃ ℝ) →
    ∃ C : Set (Set ℝ), C.Countable ∧
      ∀ S ∈ F, @MeasurableSet ℝ (MeasurableSpace.generateFrom C) S

/-- Does the countably generated family property imply that abstract
rectangles generate every subset of the real plane? -/
theorem main :
    AllContinuumFamiliesCountablyGenerated → AllSetsGeneratedByRectangles := by
  sorry

end OMA.S_mo_258842
