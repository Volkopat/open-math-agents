import Mathlib

/-! Joseph O'Rourke, MathOverflow 78026 (https://mathoverflow.net/q/78026).
We formalize the opening question, not the clarification about planar domains.
A nowhere-vanishing smooth alternating two-form characterizes orientability in
real dimension two. The metric is prescribed, not chosen after the map.
Metric and pullback formulation adapted from OpenAI, openai/math (Apache-2.0),
3344da59991ed94f9ba711217b29c1d760badfa6, ComparatorChallenges/SurfaceImmersion.
-/
namespace OMA.S_mo_78026
open Bundle Manifold
open scoped ContDiff
abbrev Plane := EuclideanSpace ℝ (Fin 2)
abbrev Space := EuclideanSpace ℝ (Fin 4)
noncomputable abbrev I₂ := 𝓘(ℝ, Plane)
noncomputable abbrev I₄ := 𝓘(ℝ, Space)

def Orientable (M : Type*) [TopologicalSpace M] [ChartedSpace Plane M] [IsManifold I₂ ∞ M] : Prop :=
  ∃ form : (p : M) → TangentSpace I₂ p →L[ℝ] TangentSpace I₂ p →L[ℝ] ℝ,
    ContMDiff I₂ (I₂.prod 𝓘(ℝ, Plane →L[ℝ] Plane →L[ℝ] ℝ)) ∞
      (fun p ↦ TotalSpace.mk' (Plane →L[ℝ] Plane →L[ℝ] ℝ) p (form p)) ∧
    (∀ p v, form p v v = 0) ∧ ∀ p, form p ≠ 0

theorem main : ∀ (M : Type*) [TopologicalSpace M] [T2Space M] [SecondCountableTopology M]
    [ChartedSpace Plane M] [IsManifold I₂ ∞ M] [CompactSpace M], Orientable M →
    ∀ g : ContMDiffRiemannianMetric I₂ ∞ Plane (fun p : M ↦ TangentSpace I₂ p),
    ∃ F : M → Space, ContMDiff I₂ I₄ ∞ F ∧
      (∀ p, Function.Injective (mfderiv I₂ I₄ F p)) ∧
      ∀ p (v w : TangentSpace I₂ p),
        inner ℝ (mfderiv I₂ I₄ F p v) (mfderiv I₂ I₄ F p w) = g.inner p v w := by
  sorry

end OMA.S_mo_78026
