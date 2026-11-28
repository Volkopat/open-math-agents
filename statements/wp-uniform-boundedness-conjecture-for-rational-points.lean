import Mathlib.Algebra.Category.ModuleCat.Differentials.Presheaf
import Mathlib.AlgebraicGeometry.Geometrically.Integral
import Mathlib.AlgebraicGeometry.Morphisms.Proper
import Mathlib.AlgebraicGeometry.Morphisms.Smooth
import Mathlib.NumberTheory.NumberField.Basic

namespace OMA.S_wp_uniform_boundedness_conjecture_for_rational_points

open AlgebraicGeometry CategoryTheory Opposite

universe u

/-- Pullback of constants, followed by restriction to each open set of the curve. -/
noncomputable def constants {K : Type u} [Field K] {C : Scheme.{u}}
    (f : C ⟶ Spec (CommRingCat.of K)) :
    (Functor.const C.Opensᵒᵖ).obj (CommRingCat.of K) ⟶ C.presheaf where
  app U :=
    ((Scheme.ΓSpecIso (CommRingCat.of K)).inv ≫ f.appTop) ≫
      C.presheaf.map (homOfLE (show U.unop ≤ ⊤ from le_top)).op
  naturality U V g := by
    let restrict (W : C.Opensᵒᵖ) : op (⊤ : C.Opens) ⟶ W :=
      (homOfLE (show W.unop ≤ ⊤ from le_top)).op
    let c : CommRingCat.of K ⟶ C.presheaf.obj (op (⊤ : C.Opens)) :=
      (Scheme.ΓSpecIso (CommRingCat.of K)).inv ≫ f.appTop
    change 𝟙 (CommRingCat.of K) ≫ (c ≫ C.presheaf.map (restrict V)) =
      (c ≫ C.presheaf.map (restrict U)) ≫ C.presheaf.map g
    rw [Category.id_comp, Category.assoc c (C.presheaf.map (restrict U)) (C.presheaf.map g)]
    rw [← C.presheaf.map_comp (restrict U) g,
      show restrict U ≫ g = restrict V from Subsingleton.elim _ _]

/-- Global regular differentials are the compatible families of Kähler
differentials on the affine opens of the curve. -/
noncomputable def genus {K : Type u} [Field K] {C : Scheme.{u}}
    (f : C ⟶ Spec (CommRingCat.of K)) : ℕ :=
  let base := constants f
  let differentials := PresheafOfModules.DifferentialsConstruction.relativeDifferentials' base
  let affineOpen := {U : C.Opens // IsAffineOpen U}
  letI : ∀ U : affineOpen, Module K (differentials.obj (op U.val)) :=
    fun U => Module.compHom (differentials.obj (op U.val)) (base.app (op U.val)).hom
  let compatible : Set ((U : affineOpen) → differentials.obj (op U.val)) :=
    {s | ∀ (U V : affineOpen) (h : V.val ≤ U.val),
      differentials.map (homOfLE h).op (s U) = s V}
  Module.finrank K (Submodule.span K compatible)

/-- Rational points of the curve are sections of its structure morphism. -/
abbrev RationalPoints {K : Type u} [Field K] {C : Scheme.{u}}
    (f : C ⟶ Spec (CommRingCat.of K)) :=
  { x : Spec (CommRingCat.of K) ⟶ C // x ≫ f = 𝟙 _ }

/-- Uniform boundedness of rational points in fixed genus over a fixed number field. -/
theorem main :
    ∀ (K : Type u) [Field K] [NumberField K] (g : ℕ), 2 ≤ g →
      ∃ bound : ℕ,
        ∀ (C : Scheme.{u}) (f : C ⟶ Spec (CommRingCat.of K)),
          Smooth f → IsProper f → GeometricallyIntegral f →
          topologicalKrullDim C = 1 → genus f = g →
          Finite (RationalPoints f) ∧ Nat.card (RationalPoints f) ≤ bound := by
  sorry

end OMA.S_wp_uniform_boundedness_conjecture_for_rational_points
