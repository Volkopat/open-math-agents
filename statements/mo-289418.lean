import Mathlib.CategoryTheory.Abelian.GrothendieckCategory.Basic
import Mathlib.CategoryTheory.Preadditive.Injective.Basic
import Mathlib.CategoryTheory.Presentable.LocallyPresentable

open CategoryTheory

namespace OMA.S_mo_289418

universe u

/-- There is a locally presentable abelian category with enough injectives
which is not a Grothendieck abelian category. -/
theorem main :
    ∃ (C : Type (u + 1)) (_ : Category.{u} C) (_ : Abelian C),
      IsLocallyPresentable.{u} C ∧ EnoughInjectives C ∧
        ¬ IsGrothendieckAbelian.{u} C := by
  sorry

end OMA.S_mo_289418
