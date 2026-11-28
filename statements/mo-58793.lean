import Mathlib

namespace OMA.S_mo_58793

open scoped ContDiff Manifold
open Manifold

abbrev Space (n : ℕ) := EuclideanSpace ℝ (Fin n)
noncomputable abbrev Model (n : ℕ) := 𝓘(ℝ, Space n)

/-- A smooth tangent frame with one vector field per dimension. -/
def HasSmoothFrame {n : ℕ} (M : Type) [TopologicalSpace M] [ChartedSpace (Space n) M]
    [IsManifold (Model n) ∞ M] : Prop :=
  ∃ frame : (x : M) → Fin n → TangentSpace (Model n) x,
    (∀ x : M, LinearIndependent ℝ (frame x)) ∧
    ∀ i : Fin n, ContMDiff (Model n) (Model n).tangent ∞
      (fun x => (⟨x, frame x i⟩ : TangentBundle (Model n) M))

/-- Can a nontrivial tangent bundle have total space diffeomorphic to the product
of its base with Euclidean space of the same dimension? -/
theorem main :
    ∃ (n : ℕ) (M : Type) (topology : TopologicalSpace M),
      letI : TopologicalSpace M := topology
      ∃ charts : ChartedSpace (Space n) M,
        letI : ChartedSpace (Space n) M := charts
        T2Space M ∧ SecondCountableTopology M ∧
        ∃ smooth : IsManifold (Model n) ∞ M,
          letI : IsManifold (Model n) ∞ M := smooth
          (¬ HasSmoothFrame (n := n) M) ∧
          Nonempty (TangentBundle (Model n) M
            ≃ₘ⟮(Model n).tangent, (Model n).prod (Model n)⟯ (M × Space n)) := by
  sorry

end OMA.S_mo_58793
