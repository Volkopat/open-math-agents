import Mathlib

/-!
# Borel conjecture

Source: https://en.wikipedia.org/wiki/Borel_conjecture
-- Credit: @Dugongue (agent: Claude Code, model claude-opus-5-5)

Conjecture (Borel): aspherical closed manifolds are determined up to homeomorphism by their
fundamental groups. In the form on the source page: if `M, N` are closed aspherical
(topological) manifolds and `f : M → N` is a homotopy equivalence, then `M` and `N` are
homeomorphic (indeed `f` is homotopic to a homeomorphism; we state the homeomorphism
version, which is the "determined up to homeomorphism" statement).

For aspherical spaces, a homotopy equivalence is the same as an isomorphism of fundamental
groups (Whitehead), so the homotopy-equivalence form is used.

Conventions. A closed `n`-manifold: a compact, connected, Hausdorff, second countable space
locally modelled on `ℝⁿ` (`ChartedSpace (EuclideanSpace ℝ (Fin n))`, no boundary).
Aspherical: path connected with `π_k(M, x)` trivial for all `k ≥ 2` and all `x`.
-/

namespace OMA.S_wp_borel_conjecture

/-- `M` is a closed topological manifold of dimension `n`. -/
class ClosedManifold (n : ℕ) (M : Type) [TopologicalSpace M]
    [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] : Prop where
  compact : CompactSpace M
  connected : ConnectedSpace M
  t2 : T2Space M
  secondCountable : SecondCountableTopology M

/-- `M` is aspherical. -/
def Aspherical (M : Type) [TopologicalSpace M] : Prop :=
  PathConnectedSpace M ∧ ∀ (k : ℕ), 2 ≤ k → ∀ x : M, Subsingleton (HomotopyGroup (Fin k) M x)

/-- Borel's conjecture. -/
theorem main :
    ∀ (m n : ℕ) (M N : Type) [TopologicalSpace M] [TopologicalSpace N]
      [ChartedSpace (EuclideanSpace ℝ (Fin m)) M] [ChartedSpace (EuclideanSpace ℝ (Fin n)) N],
      ClosedManifold m M → ClosedManifold n N → Aspherical M → Aspherical N →
      Nonempty (ContinuousMap.HomotopyEquiv M N) → Nonempty (M ≃ₜ N) := by
  sorry

end OMA.S_wp_borel_conjecture
