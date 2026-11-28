import Mathlib

/-!
# Finite-dimensional simple complex group modules and virtual abelianness

Is a group virtually abelian precisely when all simple modules over its complex
group algebra are finite dimensional over the complex numbers?

[MathOverflow question](https://mathoverflow.net/questions/309993/groups-whose-complex-irreducible-representations-are-finite-dimensional)
-/

namespace OMA.S_mo_309993

universe u

def AllSimpleModulesFinite (G : Type u) [Group G] : Prop :=
  ∀ (V : Type u) [AddCommGroup V] [Module (MonoidAlgebra ℂ G) V],
    IsSimpleModule (MonoidAlgebra ℂ G) V →
      letI : Module ℂ V := Module.compHom V (algebraMap ℂ (MonoidAlgebra ℂ G))
      FiniteDimensional ℂ V

theorem main :
    ∀ (G : Type u) [Group G],
      (∃ A : Subgroup G, A.FiniteIndex ∧ ∀ x y : A, x * y = y * x) ↔
        AllSimpleModulesFinite G := by
  sorry

end OMA.S_mo_309993
