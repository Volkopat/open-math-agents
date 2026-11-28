import Mathlib

/-!
# The weak Bombieri–Lang conjecture over number fields

A positive-dimensional variety of general type over a number field has a
proper Zariski-closed subset containing all of its rational points.

We express general type via a smooth proper birational model. A nonzero
alternating functional on the generic differentials gives a rational frame
for the canonical line. A rational pluricanonical form is global precisely
when its coefficient belongs to the corresponding lattice at every stalk.
Ratios of sections define the pluricanonical rational map. Its image has
full dimension when some such ratios form an algebraically independent family.

References:
* Bresciani, On the Bombieri–Lang conjecture over finitely generated fields,
  https://arxiv.org/abs/2012.15765
* Kollár, Moduli of varieties of general type, Chapter 1, §2,
  https://web.math.princeton.edu/~kollar/book/chap1.pdf
* The Stacks Project, smoothness and relative differentials, Tag 01V4.
* Source: https://en.wikipedia.org/wiki/Bombieri%E2%80%93Lang_conjecture

Credit: @studer
-/

namespace OMA.S_wp_bombieri_lang_conjecture

open AlgebraicGeometry CategoryTheory

universe u

/-- Coefficients of regular top differentials at x in a rational volume coordinate. -/
noncomputable def canonicalStalk (K : Type u) [Field K] (Y : Scheme.{u})
    [IsIntegral Y] [Algebra K Y.functionField] {d : ℕ}
    (vol : AlternatingMap Y.functionField (KaehlerDifferential K Y.functionField)
      Y.functionField (Fin d)) (x : Y) : Submodule (Y.presheaf.stalk x) Y.functionField :=
  Submodule.span _ (Set.range fun a : Fin d → Y.presheaf.stalk x =>
    vol fun i => KaehlerDifferential.D K Y.functionField
      (algebraMap (Y.presheaf.stalk x) Y.functionField (a i)))

/-- The generic fiber of the canonical bundle is one-dimensional. In any
rational volume coordinate, the local m-th powers below describe its
m-pluricanonical sections. A full-dimensional pluricanonical image
characterizes a positive-dimensional smooth proper model of general type. -/
noncomputable def bigCanonical (K : Type u) [Field K] (Y : Scheme.{u})
    [IsIntegral Y] (s : Y ⟶ Spec (.of K)) : Prop :=
  letI : Nonempty (⊤ : Y.Opens) := ⟨⟨genericPoint Y, Set.mem_univ _⟩⟩
  letI : Algebra K Y.functionField :=
    ((Scheme.ΓSpecIso (.of K)).inv ≫ s.appTop ≫ Y.germToFunctionField ⊤).hom.toAlgebra
  ∃ (d : ℕ), 0 < d ∧ (∃ z : Fin d → Y.functionField, IsTranscendenceBasis K z) ∧
    ∃ (vol : AlternatingMap Y.functionField (KaehlerDifferential K Y.functionField)
        Y.functionField (Fin d)), vol ≠ 0 ∧
    ∃ (m : ℕ), 0 < m ∧
      let regular := fun f : Y.functionField => ∀ x : Y, f ∈ (canonicalStalk K Y vol x)^m
      ∃ (f₀ : Y.functionField) (f : Fin d → Y.functionField),
        f₀ ≠ 0 ∧ regular f₀ ∧ (∀ i, regular (f i)) ∧
        AlgebraicIndependent K (fun i => f i / f₀)

/-- A general-type variety may be open or singular. Its smooth proper
model is taken over the same number field. -/
noncomputable def ofGeneralType (K : Type u) [Field K] {X : Scheme.{u}}
    (sX : X ⟶ Spec (.of K)) : Prop :=
  ∃ (Y : Scheme.{u}) (sY : Y ⟶ Spec (.of K)) (_ : IsIntegral Y),
    GeometricallyIntegral sY ∧ Smooth sY ∧ IsProper sY ∧
    Scheme.BirationalOver sX sY ∧ bigCanonical K Y sY

/-- Images of sections of the structure map from the spectrum of K. -/
def rationalPoints (K : Type u) [Field K] {X : Scheme.{u}} (s : X ⟶ Spec (.of K)) :
    Set X := {x | ∃ p : Spec (.of K) ⟶ X, p ≫ s = 𝟙 _ ∧
      p (IsLocalRing.closedPoint K) = x}

theorem main : ∀ (K : Type u) [Field K] [NumberField K] (X : Scheme.{u})
    (s : X ⟶ Spec (.of K)) [GeometricallyIntegral s] [IsSeparated s] [LocallyOfFiniteType s] [QuasiCompact s],
     ofGeneralType K s → ¬ Dense (rationalPoints K s) := by
  sorry

end OMA.S_wp_bombieri_lang_conjecture
