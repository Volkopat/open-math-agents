import Mathlib

/-!
# Lipschitz regularity of a convex body's radial function

Source: Luke S., https://mathoverflow.net/questions/147221 (CC BY-SA).
Lev Borisov observed the Lipschitz conclusion for polytopes in the comments.
Credit: @connoranderson. The quantitative bound below applies to closed convex
bodies in any real inner product space, for chordal and geodesic distances.
-/
namespace OMA.S_mo_147221
open Metric Set InnerProductGeometry

noncomputable def radial {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    (K : Set E) (u : E) : ℝ := sSup {t : ℝ | 0 < t ∧ t • u ∈ K}

theorem main : ∀ (E : Type) [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    (K : Set E), IsClosed K → Convex ℝ K →
    (∀ r R : ℝ, 0 < r → 0 < R → ball 0 r ⊆ K → K ⊆ closedBall 0 R →
      (∀ u : E, ‖u‖ = 1 → r ≤ radial K u ∧ radial K u ≤ R ∧ radial K u • u ∈ K) ∧
      ∀ u v : E, ‖u‖ = 1 → ‖v‖ = 1 →
        |radial K u - radial K v| ≤ R^2/r * dist u v ∧
        |radial K u - radial K v| ≤ R^2/r * angle u v) ∧
    (0 ∈ interior K → Bornology.IsBounded K →
      ContinuousOn (radial K) (sphere 0 1) ∧ ∃ C : ℝ, 0 < C ∧
        ∀ u v : E, ‖u‖ = 1 → ‖v‖ = 1 → |radial K u - radial K v| ≤ C * angle u v) := by
  sorry
end OMA.S_mo_147221
