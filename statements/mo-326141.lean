import Mathlib

namespace OMA.S_mo_326141

/-- A finite family on which the upper-set subdivision can be carried out.
The terminal sets are empty or have a least element. Each other set is
the union of two proper upper subsets, and the family also contains their intersection. -/
structure SubdivisionFamily {α : Type*} [Fintype α] [DecidableEq α]
    [PartialOrder α] (F : Finset (Finset α)) : Prop where
  containsWhole : Finset.univ ∈ F
  allUpper : ∀ U ∈ F, IsUpperSet (U : Set α)
  split : ∀ U ∈ F, U = ∅ ∨ (∃ x ∈ U, ∀ y ∈ U, x ≤ y) ∨
    ∃ V ∈ F, ∃ W ∈ F, V ⊂ U ∧ W ⊂ U ∧ V ∪ W = U ∧ V ∩ W ∈ F

/-- A choice of subdivisions visits at most (n + 1)² distinct upper sets
of a finite poset with n points. -/
theorem main :
    ∀ (α : Type*) [Fintype α] [DecidableEq α] [PartialOrder α],
      ∃ F : Finset (Finset α),
        F.card ≤ (Fintype.card α + 1) ^ 2 ∧ SubdivisionFamily F := by
  sorry

end OMA.S_mo_326141
