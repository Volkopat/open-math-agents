import Mathlib

/-!
# MathOverflow 315934

Source: https://mathoverflow.net/questions/315934
-/

namespace OMA.S_mo_315934

open CategoryTheory

/-- A natural representation by the covariant hom functor from the group A. -/
structure Representation (A : GrpCat.{0}) where
  equiv (G : GrpCat.{0}) : (A ⟶ G) ≃ {g : G // IsOfFinOrder g}
  compatible (G H : GrpCat.{0}) (f : A ⟶ G) (g : G ⟶ H) :
    (equiv H (f ≫ g)).val = g.hom (equiv G f).val

theorem main : ∃ A : GrpCat.{0}, Nonempty (Representation A) := by
  sorry

end OMA.S_mo_315934
