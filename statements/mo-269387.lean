import Mathlib

/-!
# Uniformization over finite fields?

Source https://mathoverflow.net/questions/269387/uniformization-over-finite-fields

Do two smooth projective curves of genus at least two over an algebraic
closure of a finite field always have a common finite étale cover?
-/

namespace OMA.S_mo_269387

open AlgebraicGeometry CategoryTheory Opposite

noncomputable abbrev FieldSpectrum (K : Type) [Field K] : Scheme.{0} :=
  Spec (CommRingCat.of K)

/-- Smooth proper integral curves over a field are projective. -/
def IsSmoothProjectiveCurve {K : Type} [Field K] {X : Scheme.{0}}
    (π : X ⟶ FieldSpectrum K) : Prop :=
  IsIntegral X ∧ topologicalKrullDim X = 1 ∧ Smooth π ∧ IsProper π

/-- The scalar map on sections induced by the structure morphism. -/
noncomputable def scalarSections {K : Type} [Field K] {X : Scheme.{0}}
    (π : X ⟶ FieldSpectrum K) (W : X.Opens) : K →+* Γ(X, W) :=
  ((Scheme.ΓSpecIso (CommRingCat.of K)).inv ≫ π.appTop ≫
    X.presheaf.map (homOfLE (le_top : W ≤ ⊤)).op).hom

/-- Two independent classes in the first Čech cohomology of the structure
sheaf for a two-affine cover. For a smooth projective curve over an
algebraically closed field this is equivalent to genus at least two. -/
def GenusAtLeastTwo {K : Type} [Field K] {X : Scheme.{0}}
    (π : X ⟶ FieldSpectrum K) : Prop :=
  ∃ U V : X.Opens, IsAffineOpen U ∧ IsAffineOpen V ∧ U ⊔ V = ⊤ ∧
    ∃ x y : Γ(X, U ⊓ V), ∀ (a b : K) (s : Γ(X, U)) (t : Γ(X, V)),
      scalarSections π (U ⊓ V) a * x + scalarSections π (U ⊓ V) b * y =
        (X.presheaf.map (homOfLE (inf_le_left : U ⊓ V ≤ U)).op).hom s -
        (X.presheaf.map (homOfLE (inf_le_right : U ⊓ V ≤ V)).op).hom t →
      a = 0 ∧ b = 0

theorem main :
    ∀ (p : ℕ) [Fact p.Prime], ∀ {X Y : Scheme.{0}}
      (πX : X ⟶ FieldSpectrum (AlgebraicClosure (ZMod p)))
      (πY : Y ⟶ FieldSpectrum (AlgebraicClosure (ZMod p))),
      IsSmoothProjectiveCurve πX → IsSmoothProjectiveCurve πY →
      GenusAtLeastTwo πX → GenusAtLeastTwo πY →
      ∃ (D : Scheme.{0}) (πD : D ⟶ FieldSpectrum (AlgebraicClosure (ZMod p)))
        (f : D ⟶ X) (g : D ⟶ Y),
        IsSmoothProjectiveCurve πD ∧ f ≫ πX = πD ∧ g ≫ πY = πD ∧
        IsFinite f ∧ Etale f ∧ Function.Surjective f ∧
        IsFinite g ∧ Etale g ∧ Function.Surjective g := by
  sorry

end OMA.S_mo_269387
