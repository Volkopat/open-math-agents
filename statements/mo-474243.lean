import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Geometry.Manifold.Diffeomorph

namespace OMA.S_mo_474243

open scoped ContDiff Manifold

universe u

abbrev Model (n : ℕ) := EuclideanSpace ℝ (Fin n)

/-- A smooth atlas on the fixed underlying topological space. -/
def SmoothAtlas (n : ℕ) (M : Type u) [TopologicalSpace M] : Type u :=
  {A : ChartedSpace (Model n) M // letI := A; IsManifold (𝓘(ℝ, Model n)) ∞ M}

/-- Isomorphism of the smooth manifolds determined by two atlases on the same space. -/
def Diffeomorphic {n : ℕ} {M : Type u} [TopologicalSpace M]
    (A B : SmoothAtlas n M) : Prop :=
  Nonempty (@Diffeomorph ℝ _ (Model n) _ _ (Model n) _ _ (Model n) _ (Model n) _
    (𝓘(ℝ, Model n)) (𝓘(ℝ, Model n)) M _ A.1 M _ B.1 ∞)

/-- Smooth structures on a connected, Hausdorff, second-countable topological
manifold have at most countably many or continuum many diffeomorphism classes. -/
theorem main :
    ∀ (n : ℕ) (M : Type u) [TopologicalSpace M] [ChartedSpace (Model n) M]
      [ConnectedSpace M] [T2Space M] [SecondCountableTopology M],
      let classes := Quot (Diffeomorphic (n := n) (M := M))
      Countable classes ∨ Nonempty (classes ≃ ℝ) := by
  sorry

end OMA.S_mo_474243
