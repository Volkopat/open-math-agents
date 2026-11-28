import Mathlib

namespace OMA.S_mo_480802

open Manifold
open scoped ContDiff Manifold

abbrev Space (d : ℕ) := EuclideanSpace ℝ (Fin d)
abbrev Ambient := Space 6
abbrev AmbientForm (d : ℕ) := AlternatingMap ℝ Ambient ℝ (Fin d)

/-- The ambient forms specify an orientation by evaluating nontrivially on
each tangent frame of the embedded manifold. Continuity is joint in the point and frame. -/
def Orients {d : ℕ} {X : Type} [TopologicalSpace X]
    (tangentMap : X → (Space d →L[ℝ] Ambient)) (forms : X → AmbientForm d) : Prop :=
  Continuous (fun p : X × (Fin d → Ambient) => forms p.1 p.2) ∧
    ∀ (x : X) (frame : Fin d → Space d), LinearIndependent ℝ frame →
      forms x (fun i => tangentMap x (frame i)) ≠ 0

/-- Compare the prescribed orientation with the outward-vector-first boundary
orientation at points representing the same ambient point. -/
def AgreesOnBoundary {M W : Type} [TopologicalSpace M] [TopologicalSpace W]
    [ChartedSpace (Space 3) M] [ChartedSpace (EuclideanHalfSpace 4) W]
    (f : M → Ambient) (g : W → Ambient)
    (formsM : M → AmbientForm 3) (formsW : W → AmbientForm 4) : Prop :=
  ∀ w ∈ (𝓡∂ 4).boundary W, ∀ x : M, g w = f x →
    ∃ normal : Space 4,
      let chartDerivative : Space 4 →L[ℝ] Space 4 :=
        mfderiv (𝓡∂ 4) (𝓡 4) (extChartAt (𝓡∂ 4) w : W → Space 4) w
      chartDerivative normal 0 < 0 ∧
        ∀ frame : Fin 3 → Space 3, LinearIndependent ℝ frame →
          let tangentFrame : Fin 3 → Ambient :=
            fun i => mfderiv (𝓡 3) (𝓡 6) f x (frame i)
          0 < formsM x tangentFrame ↔
            0 < formsW w (Fin.cons (mfderiv (𝓡∂ 4) (𝓡 6) g w normal) tangentFrame)

/-- Every compact oriented boundaryless smooth 3-submanifold of six-space is
the oriented boundary of a compact smooth 4-submanifold of the same six-space. -/
theorem main :
    ∀ (M : TopCat) [T2Space M] [CompactSpace M]
      [ChartedSpace (Space 3) M] [IsManifold (𝓡 3) ∞ M],
      ∀ (f : M → Ambient) (formsM : M → AmbientForm 3),
        IsSmoothEmbedding (𝓡 3) (𝓡 6) ∞ f →
        Orients (fun x => mfderiv (𝓡 3) (𝓡 6) f x) formsM →
        ∃ (W : TopCat) (charts : ChartedSpace (EuclideanHalfSpace 4) W),
          letI := charts
          T2Space W ∧ CompactSpace W ∧ IsManifold (𝓡∂ 4) ∞ W ∧
            ∃ (g : W → Ambient) (formsW : W → AmbientForm 4),
              IsSmoothEmbedding (𝓡∂ 4) (𝓡 6) ∞ g ∧
              Orients (fun w => mfderiv (𝓡∂ 4) (𝓡 6) g w) formsW ∧
              g '' (𝓡∂ 4).boundary W = Set.range f ∧
              AgreesOnBoundary f g formsM formsW := by
  sorry

end OMA.S_mo_480802
