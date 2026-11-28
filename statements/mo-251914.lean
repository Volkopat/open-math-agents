import Mathlib

/-!
# A witness criterion for Brendan Fong's pushout–pullback question

Source: Brendan Fong, MathOverflow 251914, 11 October 2016.
https://mathoverflow.net/questions/251914
Formalisation: @lawrencerowland, with Codex.

Fong asks for conditions under which the comparison belongs to the left
class E of a stable factorisation system. This proposed answer tests any
cospan on the two endpoints. It suffices that its pullback receive the
original span through an E-map. The theorem applies to all spans in the
specified subcategory A, including the cases E ⊆ A and A = E. The source
does not prescribe a unique criterion or ask for an unconditional assertion.
-/

open CategoryTheory CategoryTheory.Limits

universe v u

namespace OMA.S_mo_251914

/-- Uniqueness of diagonal fillers for the two classes of a weak
factorisation system makes it an orthogonal factorisation system. -/
def UniqueFillers {C : Type u} [Category.{v} C] (E M : MorphismProperty C) : Prop :=
  ∀ {U V S T : C} (e : U ⟶ V) (m : S ⟶ T), E e → M m →
    ∀ (a : U ⟶ S) (b : V ⟶ T), a ≫ m = e ≫ b →
      ∃! d : V ⟶ S, e ≫ d = a ∧ d ≫ m = b

theorem main :
    ∀ {C : Type u} [Category.{v} C] [HasPullbacks C] [HasPushouts C]
      (E M A : MorphismProperty C) [E.IsWeakFactorizationSystem M]
      [E.IsStableUnderBaseChange], UniqueFillers E M →
      MorphismProperty.isomorphisms C ≤ A →
      ∀ [A.IsStableUnderComposition] [A.IsStableUnderCobaseChange]
        {N X Y : C} (f : N ⟶ X) (g : N ⟶ Y), A f → A g →
        (E (pullback.lift f g (pushout.condition (f := f) (g := g))) ↔
          ∃ (T : C) (i : X ⟶ T) (j : Y ⟶ T) (h : f ≫ i = g ≫ j),
            E (pullback.lift f g h)) := by
  sorry

end OMA.S_mo_251914
