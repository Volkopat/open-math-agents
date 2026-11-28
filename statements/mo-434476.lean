import Mathlib

/-!
# Tim Campion’s question about pushouts of arrows

Source: Tim Campion, MathOverflow 434476, 12 November 2022.
https://mathoverflow.net/questions/434476
Formalisation: @lawrencerowland, with Codex.

This is the proposed implication (0) + (2) + (3) ⇒ (1). The final property
is closure of the class of arrows under pushouts in the arrow category:
colimits there are computed at the domain and codomain. Cancellation says
that a composite and its first factor in the class force the second factor
into the class. Campion separately discusses adding composition closure.
-/

open CategoryTheory CategoryTheory.Limits

namespace OMA.S_mo_434476

theorem main :
    ∀ (C : Type) [Category.{0} C] [HasPushouts C] (L : MorphismProperty C),
      L.ContainsIdentities → L.IsStableUnderCobaseChange →
      L.HasOfPrecompProperty L → L.IsStableUnderColimitsOfShape WalkingSpan := by
  sorry

end OMA.S_mo_434476
