import Mathlib

/-!
# Borel partition of Euclidean three-space into unit circles

Source https://mathoverflow.net/q/93601

The unit-circle case of Question 1 asks whether every partition of
Euclidean three-space into unit circles has a non-Borel same-circle
relation. The author restates this case in the discussion at
https://mathoverflow.net/q/481197. See also https://arxiv.org/abs/2501.03131.
-/

namespace OMA.S_mo_93601

abbrev Space := EuclideanSpace ℝ (Fin 3)

/-- The radius-one sphere in an affine two-plane through its center. -/
def IsUnitCircle (s : Set Space) : Prop :=
  ∃ (center : Space) (plane : Submodule ℝ Space),
    Module.finrank ℝ plane = 2 ∧
      s = {x | x - center ∈ plane ∧ dist x center = 1}

/-- Borelness refers to the same-circle relation on the product space. -/
def IsBorelUnitCirclePartition (parts : Set (Set Space)) : Prop :=
  (∀ s ∈ parts, IsUnitCircle s) ∧
  (∀ x : Space, ∃! s : Set Space, s ∈ parts ∧ x ∈ s) ∧
  MeasurableSet {xy : Space × Space | ∃ s ∈ parts, xy.1 ∈ s ∧ xy.2 ∈ s}

theorem main :
    ¬ ∃ parts : Set (Set Space), IsBorelUnitCirclePartition parts := by
  sorry

end OMA.S_mo_93601
