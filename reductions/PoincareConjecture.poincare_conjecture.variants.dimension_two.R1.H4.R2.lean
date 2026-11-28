import OMAReductions.R_PoincareConjecture_poincare_conjecture_variants_dimension_two_R1
import Mathlib.Topology.Compactification.OnePoint.Sphere

namespace OMA.R_PoincareConjecture_poincare_conjecture_variants_dimension_two_R1_H4_R2

open scoped Manifold ContDiff

/-- A closed simply connected topological surface admits a complex atlas. -/
def H1 : Prop := ∀ (M : Type) [TopologicalSpace M] [T2Space M]
    [ChartedSpace (EuclideanSpace ℝ (Fin 2)) M] [SimplyConnectedSpace M] [CompactSpace M],
    ∃ atlas : ChartedSpace ℂ M, letI := atlas; IsManifold 𝓘(ℂ) ω M

/-- Uniformization realizes a simply connected Riemann surface as a domain in the Riemann sphere. -/
def H2 : Prop := ∀ (M : Type) [TopologicalSpace M] [T2Space M] [SecondCountableTopology M]
    [ChartedSpace ℂ M] [IsManifold 𝓘(ℂ) ω M] [SimplyConnectedSpace M],
    ∃ f : M → OnePoint ℂ, Topology.IsOpenEmbedding f

theorem main : H1 → H2 → OMA.R_PoincareConjecture_poincare_conjecture_variants_dimension_two_R1.H4 := by
  intro charts uniformize M _ _ _ _ _
  obtain ⟨atlas, analytic⟩ := charts M
  let _ := atlas
  have : IsManifold 𝓘(ℂ) ω M := analytic
  have := ChartedSpace.secondCountable_of_sigmaCompact ℂ M
  obtain ⟨f, embedding⟩ := uniformize M
  have closed : IsClosed (Set.range f) := (isCompact_range embedding.continuous).isClosed
  have full := IsClopen.eq_univ ⟨closed, embedding.isOpen_range⟩ (Set.range_nonempty f)
  exact ⟨(embedding.toHomeomorphOfSurjective (Set.range_eq_univ.mp full)).trans
    (onePointEquivSphereOfFinrankEq (by simp))⟩

end OMA.R_PoincareConjecture_poincare_conjecture_variants_dimension_two_R1_H4_R2
