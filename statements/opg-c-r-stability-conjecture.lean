import Mathlib

namespace OMA.S_opg_c_r_stability_conjecture

open scoped ContDiff Manifold
open Manifold

noncomputable section

abbrev Space (d : ℕ) := EuclideanSpace ℝ (Fin d)

abbrev Model (d : ℕ) := 𝓘(ℝ, Space d)

structure Diffeomorphism (d : ℕ) (M : Type) [TopologicalSpace M]
    [ChartedSpace (Space d) M] (r : ℕ∞) where
  equiv : M ≃ M
  smooth : ContMDiff (Model d) (Model d) r (equiv : M → M)
  smoothInverse : ContMDiff (Model d) (Model d) r (equiv.symm : M → M)

/-- A Whitney embedding and a smooth retraction from an open neighborhood of its image. -/
structure AmbientModel (d e : ℕ) (M : Type) [TopologicalSpace M]
    [ChartedSpace (Space d) M] where
  embed : M → Space e
  embedding : IsSmoothEmbedding (Model d) (Model e) ∞ embed
  neighborhood : Set (Space e)
  openNeighborhood : IsOpen neighborhood
  imageInNeighborhood : Set.range embed ⊆ neighborhood
  retract : Space e → M
  smoothRetract : ContMDiffOn (Model e) (Model d) ∞ retract neighborhood
  leftInverse : Function.LeftInverse retract embed

section Definitions

variable {d e : ℕ} {M : Type} [TopologicalSpace M] [ChartedSpace (Space d) M]

/-- Use uniform ambient derivative bounds along the embedded compact manifold. -/
def AmbientModel.Close (A : AmbientModel d e M) (order : ℕ) (ε : ℝ)
    (f g : M → M) : Prop :=
  ∀ (x : M) (j : ℕ), j ≤ order →
    ‖iteratedFDeriv ℝ j (A.embed ∘ f ∘ A.retract) (A.embed x) -
      iteratedFDeriv ℝ j (A.embed ∘ g ∘ A.retract) (A.embed x)‖ < ε

/-- A whole C^r neighborhood in the diffeomorphism space has the same conjugacy type. -/
def IsStructurallyStable {r : ℕ∞} (A : AmbientModel d e M)
    (f : Diffeomorphism d M r) : Prop :=
  ∃ (order : ℕ) (ε : ℝ), (order : ℕ∞) ≤ r ∧ 0 < ε ∧
    ∀ g : Diffeomorphism d M r, A.Close order ε f.equiv g.equiv →
      ∃ h : M ≃ₜ M, ∀ x : M, h (f.equiv x) = g.equiv (h x)

def nonwandering (f : M → M) : Set M :=
  {x | ∀ U : Set M, IsOpen U → x ∈ U →
    ∃ n : ℕ, 0 < n ∧ ∃ y ∈ U, (f^[n]) y ∈ U}

def periodic (f : M → M) : Set M :=
  {x | ∃ n : ℕ, 0 < n ∧ (f^[n]) x = x}

noncomputable def AmbientModel.tangentNorm (A : AmbientModel d e M) (x : M)
    (v : TangentSpace (Model d) x) : ℝ :=
  let w : Space e := mfderiv (Model d) (Model e) A.embed x v
  ‖w‖

/-- Use ambient orthogonal projections to express continuity of the subspaces. -/
noncomputable def AmbientModel.tangentProjection (A : AmbientModel d e M) (x : M)
    (S : Submodule ℝ (TangentSpace (Model d) x)) : Space e →L[ℝ] Space e :=
  let derivative : TangentSpace (Model d) x →ₗ[ℝ] Space e :=
    (mfderiv (Model d) (Model e) A.embed x).toLinearMap
  (S.map derivative).starProjection

def UniformlyHyperbolic {r : ℕ∞} (A : AmbientModel d e M)
    (f : Diffeomorphism d M r) (K : Set M) : Prop :=
  let forward : M → M := f.equiv
  let backward : M → M := f.equiv.symm
  ∃ stable unstable : (x : M) → Submodule ℝ (TangentSpace (Model d) x),
    ContinuousOn (fun x => A.tangentProjection x (stable x)) K ∧
    ContinuousOn (fun x => A.tangentProjection x (unstable x)) K ∧
    (∀ x ∈ K, IsCompl (stable x) (unstable x) ∧
      (stable x).map (mfderiv (Model d) (Model d) forward x).toLinearMap =
        stable (forward x) ∧
      (unstable x).map (mfderiv (Model d) (Model d) forward x).toLinearMap =
        unstable (forward x)) ∧
    ∃ (C rate : ℝ), 0 < C ∧ 0 < rate ∧ rate < 1 ∧
      ∀ (n : ℕ) (x : M), x ∈ K →
        (∀ v ∈ stable x,
          A.tangentNorm ((forward^[n]) x) (mfderiv (Model d) (Model d) (forward^[n]) x v) ≤
            C * rate ^ n * A.tangentNorm x v) ∧
        (∀ v ∈ unstable x,
          A.tangentNorm ((backward^[n]) x) (mfderiv (Model d) (Model d) (backward^[n]) x v) ≤
            C * rate ^ n * A.tangentNorm x v)

end Definitions

/-- Palis–Smale necessity: a C^r structurally stable diffeomorphism of a closed
smooth manifold has a hyperbolic nonwandering set with dense periodic points. -/
theorem main :
    ∀ (d e : ℕ) (M : Type) [TopologicalSpace M] [T2Space M] [CompactSpace M]
      [Nonempty M] [ChartedSpace (Space d) M] [IsManifold (Model d) ∞ M],
      ∀ (A : AmbientModel d e M) (r : ℕ∞), 1 ≤ r →
        ∀ f : Diffeomorphism d M r, IsStructurallyStable A f →
          closure (periodic f.equiv) = nonwandering f.equiv ∧
          UniformlyHyperbolic A f (nonwandering f.equiv) := by
  sorry

end

end OMA.S_opg_c_r_stability_conjecture
