import Mathlib.AlgebraicGeometry.Geometrically.Integral
import Mathlib.AlgebraicGeometry.Morphisms.Proper
import Mathlib.AlgebraicGeometry.Morphisms.Smooth
import Mathlib.CategoryTheory.Comma.Over.Pullback
import Mathlib.FieldTheory.AlgebraicClosure

namespace OMA.S_mo_418626

open AlgebraicGeometry CategoryTheory

universe u

/-- Every finite group is the full automorphism group of a smooth projective
curve over the given field, with all geometric automorphisms defined over that field.
For a curve over a field, properness is equivalent to projectivity. -/
theorem main :
    ∀ (k : Type u) [Field k] (G : Type u) [Group G] [Finite G],
      let base := Spec (CommRingCat.of k)
      let extension := Spec.map (CommRingCat.ofHom (algebraMap k (AlgebraicClosure k)))
      ∃ (C : Scheme.{u}) (f : C ⟶ base),
        Smooth f ∧ IsProper f ∧ GeometricallyIntegral f ∧
          topologicalKrullDim C = 1 ∧
          Nonempty (G ≃* Aut (Over.mk f)) ∧
          Function.Bijective (fun a : Aut (Over.mk f) => (Over.pullback extension).mapIso a) := by
  sorry

end OMA.S_mo_418626
