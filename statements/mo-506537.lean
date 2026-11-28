import Mathlib

/-!
# Haar scaling by a finite free module automorphism

For a second-countable locally compact Hausdorff commutative topological ring,
does a finite free module automorphism scale additive Haar measure by the same
factor as multiplication by its determinant scales additive Haar measure on the ring?

[MathOverflow question](https://mathoverflow.net/questions/506537/how-does-an-automorphism-of-a-free-module-scale-haar-measure)
-/

open MeasureTheory

namespace OMA.S_mo_506537

def ScalesMeasure {X : Type*} [MeasurableSpace X] (f : X → X)
    (μ : Measure X) (c : ℝ) : Prop :=
  ∀ s : Set X, MeasurableSet s → μ (f '' s) = ENNReal.ofReal c * μ s

theorem main :
    ∀ (R : Type) [CommRing R] [TopologicalSpace R] [IsTopologicalRing R]
      [T2Space R] [LocallyCompactSpace R] [SecondCountableTopology R]
      [MeasurableSpace R] [BorelSpace R],
      ∀ (n : ℕ) (e : (Fin n → R) ≃ₗ[R] (Fin n → R))
        (μ : Measure R) (ν : Measure (Fin n → R)),
        μ.IsAddHaarMeasure → ν.IsAddHaarMeasure →
        ∃ c : ℝ, 0 < c ∧
          ScalesMeasure (fun x : R => (LinearEquiv.det e : R) * x) μ c ∧
          ScalesMeasure e ν c := by
  sorry

end OMA.S_mo_506537
