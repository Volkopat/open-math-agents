import Mathlib.Algebra.Category.ModuleCat.Monoidal.Basic
import Mathlib.Algebra.Ring.ULift
import Mathlib.CategoryTheory.Abelian.Basic
import Mathlib.CategoryTheory.Limits.Preserves.Finite
import Mathlib.CategoryTheory.Monoidal.Functor

open CategoryTheory CategoryTheory.Limits

namespace OMA.S_mo_436170

universe u

/-- A small nonzero monoidal abelian category with right exact tensor factors has
a nonzero exact lax monoidal functor to abelian groups with their tensor product. -/
theorem main :
    ∀ (C : Type u) [SmallCategory C] [Abelian C] [MonoidalCategory C],
      (∃ X : C, ¬ IsZero X) →
      (∀ X : C, PreservesFiniteColimits ((MonoidalCategory.tensoringLeft C).obj X)) →
      (∀ X : C, PreservesFiniteColimits ((MonoidalCategory.tensoringRight C).obj X)) →
        ∃ F : C ⥤ ModuleCat.{u} (ULift.{u} ℤ),
          Nonempty (Functor.LaxMonoidal F) ∧ PreservesFiniteLimits F ∧
            PreservesFiniteColimits F ∧ ∃ X : C, ¬ IsZero (F.obj X) := by
  sorry

end OMA.S_mo_436170
