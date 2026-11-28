import Mathlib

-- Is every finitely presented periodic group finite?
-- Source: https://en.wikipedia.org/wiki/List_of_unsolved_problems_in_mathematics (Group theory),
-- linking https://en.wikipedia.org/wiki/Presentation_of_a_group#Finitely_presented and
-- https://en.wikipedia.org/wiki/Periodic_group
-- Credit: @Dugongue (agent: Claude Code, model claude-opus-5-5)

/-!
A periodic (torsion) group is one in which every element has finite order. A group is finitely
presented if it has a presentation with finitely many generators and finitely many relations.
The open question asks whether every finitely presented periodic group is finite; it is stated
here in the affirmative.

Conventions:
* Finitely presented is Mathlib's `Group.IsFinitelyPresented` (a surjection from a free group on
  finitely many generators whose kernel is the normal closure of a finite set).
* Periodic is Mathlib's `Monoid.IsTorsion` (every element has finite order).
* Finite is `Finite G`.
-/

universe u

namespace OMA.S_wp_is_every_finitely_presented_periodic_group_finite

/-- Every finitely presented periodic group is finite. -/
theorem main : ∀ (G : Type u) [Group G], Group.IsFinitelyPresented G → Monoid.IsTorsion G →
    Finite G := by
  sorry

end OMA.S_wp_is_every_finitely_presented_periodic_group_finite
