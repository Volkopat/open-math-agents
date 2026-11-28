import Mathlib.AlgebraicGeometry.Geometrically.Integral
import Mathlib.AlgebraicGeometry.Morphisms.QuasiCompact
import Mathlib.AlgebraicGeometry.Morphisms.Separated
import Mathlib.AlgebraicGeometry.Morphisms.Smooth
import Mathlib.FieldTheory.Galois.Basic

namespace OMA.S_arxiv_2610_41843

open AlgebraicGeometry CategoryTheory

universe u

/-- A prime is prime to the absolute Galois group if it divides no finite Galois degree. -/
def PrimeToAbsoluteGaloisGroup (K : Type u) [Field K] (p : ℕ) : Prop :=
  ∀ (L : Type u) [Field L] [Algebra K L] [FiniteDimensional K L] [IsGalois K L],
    ¬ p ∣ Module.finrank K L

/-- Rational points are sections of the structure morphism. -/
abbrev RationalPoints {K : Type u} [Field K] {C : Scheme.{u}}
    (f : C ⟶ Spec (CommRingCat.of K)) :=
  { x : Spec (CommRingCat.of K) ⟶ C // x ≫ f = 𝟙 _ }

/-- A large field has infinitely many rational points on any smooth geometrically
integral curve over it that has a rational point. -/
def IsLarge (K : Type u) [Field K] : Prop :=
  ∀ (C : Scheme.{u}) (f : C ⟶ Spec (CommRingCat.of K)),
    Smooth f → QuasiCompact f → IsSeparated f → GeometricallyIntegral f →
    topologicalKrullDim C = 1 →
      Nonempty (RationalPoints f) → Infinite (RationalPoints f)

/-- A field whose absolute Galois group is prime to some prime is large. -/
theorem main :
    ∀ (K : Type u) [Field K] (p : ℕ), p.Prime →
      PrimeToAbsoluteGaloisGroup K p → IsLarge K := by
  sorry

end OMA.S_arxiv_2610_41843
