import OMAReductions.R_PoincareConjecture_poincare_conjecture_R1_H4_R1_H2_R1
import Mathlib.Geometry.Manifold.VectorBundle.Tangent
import Mathlib.LinearAlgebra.Orientation

/-!
Separate the orientability input from the geometric construction of the
spherical immersion. The orientation is a section of the tangent orientation
cover expressed in local trivializations.
-/

open Bundle Manifold Set
open scoped Manifold ContDiff EuclideanGeometry Topology

namespace OMA.R_PoincareConjecture_poincare_conjecture_R1_H4_R1_H2_R1_H1_R1

def H1 : Prop :=
  ∀ (M : Type) [TopologicalSpace M] [ChartedSpace (ℝ^3) M]
    [IsManifold (𝓡 3) ∞ M] [SimplyConnectedSpace M],
    let V := TangentSpace (𝓡 3) (M := M)
    ∃ o : ∀ x, Orientation ℝ (V x) (Fin 3),
      ∀ x, ∃ t : Trivialization (ℝ^3) (π (ℝ^3) V), ∃ _ht : MemTrivializationAtlas t,
        ∃ U ∈ 𝓝 x, ∃ hU : U ⊆ t.baseSet, ∃ q : Orientation ℝ (ℝ^3) (Fin 3),
          ∀ y (hy : y ∈ U),
            Orientation.map (Fin 3) (t.continuousLinearEquivAt ℝ y (hU hy)).toLinearEquiv
              (o y) = q

def H2 : Prop :=
  ∀ (M : Type) [TopologicalSpace M] [T2Space M] [ChartedSpace (ℝ^3) M]
    [CompactSpace M] [SecondCountableTopology M] [IsManifold (𝓡 3) ∞ M]
    [SimplyConnectedSpace M],
    let V := TangentSpace (𝓡 3) (M := M)
    ∀ (o : ∀ x, Orientation ℝ (V x) (Fin 3)),
      (∀ x, ∃ t : Trivialization (ℝ^3) (π (ℝ^3) V), ∃ _ht : MemTrivializationAtlas t,
        ∃ U ∈ 𝓝 x, ∃ hU : U ⊆ t.baseSet, ∃ q : Orientation ℝ (ℝ^3) (Fin 3),
          ∀ y (hy : y ∈ U),
            Orientation.map (Fin 3) (t.continuousLinearEquivAt ℝ y (hU hy)).toLinearEquiv
              (o y) = q) →
      ∃ f : Metric.sphere (0 : EuclideanSpace ℝ (Fin 4)) 1 → M,
        ContMDiff (𝓡 3) (𝓡 3) ∞ f ∧ ∀ x, Function.Injective (mfderiv (𝓡 3) (𝓡 3) f x)

theorem main : H1 → H2 → OMA.R_PoincareConjecture_poincare_conjecture_R1_H4_R1_H2_R1.H1 := by
  intro orientation geometry M _ _ _ _ _ _ _
  obtain ⟨o, ho⟩ := orientation M
  exact geometry M o ho

end OMA.R_PoincareConjecture_poincare_conjecture_R1_H4_R1_H2_R1_H1_R1
