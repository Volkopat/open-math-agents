import Mathlib.Algebra.Category.Ring.FilteredColimits
import Mathlib.RingTheory.Noetherian.Basic
import Mathlib.RingTheory.UniqueFactorizationDomain.Basic

open CategoryTheory CategoryTheory.Limits

namespace OMA.S_mo_470348

universe u

/-- A non-Noetherian unique factorization domain is a filtered colimit of
Noetherian unique factorization domains in the category of commutative rings. -/
theorem main :
    ∀ (R : Type u) [CommRing R],
      IsDomain R → UniqueFactorizationMonoid R → ¬ IsNoetherianRing R →
        ∃ (J : Type u) (_ : SmallCategory J) (_ : IsFiltered J)
          (F : J ⥤ CommRingCat.{u}) (c : Cocone F),
          (∀ j : J, IsDomain (F.obj j) ∧ UniqueFactorizationMonoid (F.obj j) ∧
            IsNoetherianRing (F.obj j)) ∧
              Nonempty (IsColimit c) ∧ Nonempty (c.pt ≅ CommRingCat.of R) := by
  sorry

end OMA.S_mo_470348
