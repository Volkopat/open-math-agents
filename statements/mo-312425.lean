import Mathlib.CategoryTheory.Category.RelCat

/-!
# MathOverflow 312425

Source: https://mathoverflow.net/questions/312425

Every endofunctor on the category of sets and relations that is monotone
with respect to inclusion of relations preserves the converse of a relation.
The assertion also applies to the underlying functor of any monotone monad.
-/

namespace OMA.S_mo_312425

open CategoryTheory

universe u

theorem main : ∀ (F : RelCat.{u} ⥤ RelCat.{u}),
    (∀ {X Y : RelCat.{u}} {R S : X ⟶ Y},
      R.rel ⊆ S.rel → (F.map R).rel ⊆ (F.map S).rel) →
    ∀ {X Y : RelCat.{u}} (R : X ⟶ Y),
      F.map (RelCat.Hom.ofRel R.rel.inv) =
        RelCat.Hom.ofRel (F.map R).rel.inv := by
  sorry

end OMA.S_mo_312425
