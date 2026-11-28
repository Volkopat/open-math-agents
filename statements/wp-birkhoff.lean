import Mathlib

/-!
# Birkhoff conjecture (billiards)

Source: https://en.wikipedia.org/wiki/George_David_Birkhoff
If a billiard table is strictly convex and integrable, is its boundary necessarily an
ellipse? `main` states the affirmative answer.

Conventions (Birkhoff integrability).
* The table is a compact strictly convex set `Ω ⊆ ℝ²` with nonempty interior whose boundary is
  a smooth regular closed curve `γ` (smooth, `1`-periodic, injective on `[0, 1)`, `γ' ≠ 0`).
* Billiard law: the ball travelling from `p` to `q` (both on the boundary) leaves `q` towards
  `q'` when `q' - q` is a positive multiple of the reflection of `q - p` in the tangent line at
  `q`.
* A caustic is a compact convex set `D` with nonempty interior, contained in the interior of
  `Ω`, such that whenever the line `pq` of a billiard segment supports `D`, so does the line of
  the next segment.
* The table is integrable when the boundaries of caustics cover a collar
  `{x ∈ interior Ω | dist x (∂Ω) < δ}` of the boundary (a neighbourhood of the boundary is
  foliated by convex caustics).
* An ellipse (with its interior) is an affine image of the closed unit disc.

-- Credit: @Dugongue (agent: Claude Code, model claude-opus-5-5)
-/

namespace OMA.S_wp_birkhoff

open Set Metric
open scoped ContDiff

/-- The 2D cross product `u₀ v₁ - u₁ v₀`. -/
def cross (u v : EuclideanSpace ℝ (Fin 2)) : ℝ := u 0 * v 1 - u 1 * v 0

/-- The line through `p ≠ q` supports `D`: it meets `D` and `D` lies on one side of it. -/
def Supports (D : Set (EuclideanSpace ℝ (Fin 2))) (p q : EuclideanSpace ℝ (Fin 2)) : Prop :=
  p ≠ q ∧ (∃ z ∈ D, cross (q - p) (z - p) = 0) ∧
    ((∀ z ∈ D, 0 ≤ cross (q - p) (z - p)) ∨ ∀ z ∈ D, cross (q - p) (z - p) ≤ 0)

/-- Reflection of `v` in the line spanned by `τ`. -/
noncomputable def reflectIn (τ v : EuclideanSpace ℝ (Fin 2)) : EuclideanSpace ℝ (Fin 2) :=
  (2 * inner ℝ v τ / ‖τ‖ ^ 2) • τ - v

/-- `γ` is a smooth regular closed curve parametrising `S`. -/
def SmoothBoundary (γ : ℝ → EuclideanSpace ℝ (Fin 2)) (S : Set (EuclideanSpace ℝ (Fin 2))) :
    Prop :=
  ContDiff ℝ ∞ γ ∧ Function.Periodic γ 1 ∧ InjOn γ (Ico 0 1) ∧
    (∀ t, deriv γ t ≠ 0) ∧ range γ = S

/-- Billiard step `p → γ t → q'` on the boundary curve `γ`. -/
def BilliardStep (γ : ℝ → EuclideanSpace ℝ (Fin 2)) (p : EuclideanSpace ℝ (Fin 2)) (t : ℝ)
    (q' : EuclideanSpace ℝ (Fin 2)) : Prop :=
  p ∈ range γ ∧ q' ∈ range γ ∧ p ≠ γ t ∧ q' ≠ γ t ∧
    ∃ c : ℝ, 0 < c ∧ q' - γ t = c • reflectIn (deriv γ t) (γ t - p)

/-- `D` is a convex caustic of the billiard in `Ω` with boundary curve `γ`. -/
def IsCaustic (Ω : Set (EuclideanSpace ℝ (Fin 2))) (γ : ℝ → EuclideanSpace ℝ (Fin 2))
    (D : Set (EuclideanSpace ℝ (Fin 2))) : Prop :=
  IsCompact D ∧ Convex ℝ D ∧ (interior D).Nonempty ∧ D ⊆ interior Ω ∧
    ∀ p t q', BilliardStep γ p t q' → Supports D p (γ t) → Supports D (γ t) q'

theorem main :
    ∀ (Ω : Set (EuclideanSpace ℝ (Fin 2))) (γ : ℝ → EuclideanSpace ℝ (Fin 2)),
      IsCompact Ω → StrictConvex ℝ Ω → (interior Ω).Nonempty →
      SmoothBoundary γ (frontier Ω) →
      (∃ δ > 0, ∀ x ∈ interior Ω, infDist x (frontier Ω) < δ →
        ∃ D, IsCaustic Ω γ D ∧ x ∈ frontier D) →
      ∃ A : EuclideanSpace ℝ (Fin 2) ≃ᵃ[ℝ] EuclideanSpace ℝ (Fin 2),
        Ω = A '' closedBall 0 1 := by
  sorry

end OMA.S_wp_birkhoff
