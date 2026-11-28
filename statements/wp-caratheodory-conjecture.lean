import Mathlib

/-!
# Carathéodory conjecture

Source: https://en.wikipedia.org/wiki/Carathéodory_conjecture
Any convex, closed, twice-differentiable surface in three-dimensional Euclidean space admits
at least two umbilical points.

Conventions. The surface is the boundary `S` of a compact convex body `K ⊆ ℝ³` (nonempty
interior). It is `C²` when near every `p ∈ S` it is, after a rotation `Φ` taking the tangent
plane to the first two coordinates, the graph of a `C²` function `h` on a neighbourhood of
`0 ∈ ℝ²` with `h 0 = 0` and `Dh 0 = 0` (a `GraphChart`). In such a chart the second
fundamental form at `p` is the Hessian of `h` at `0`, so `p` is umbilical exactly when this
Hessian is a scalar multiple of the inner product.

-- Credit: @Dugongue (agent: Claude Code, model claude-opus-5-5)
-/

namespace OMA.S_wp_caratheodory_conjecture

open Set

/-- The point of the chart over `x ∈ ℝ²`: `p + Φ (x₀, x₁, h x)`. -/
noncomputable def chartPoint (p : EuclideanSpace ℝ (Fin 3))
    (Φ : EuclideanSpace ℝ (Fin 3) ≃ₗᵢ[ℝ] EuclideanSpace ℝ (Fin 3))
    (h : EuclideanSpace ℝ (Fin 2) → ℝ) (x : EuclideanSpace ℝ (Fin 2)) :
    EuclideanSpace ℝ (Fin 3) :=
  p + Φ (x 0 • EuclideanSpace.single 0 1 + x 1 • EuclideanSpace.single 1 1 +
    h x • EuclideanSpace.single 2 1)

/-- `S` is, near `p`, the graph over its tangent plane of the `C²` function `h`. -/
def GraphChart (S : Set (EuclideanSpace ℝ (Fin 3))) (p : EuclideanSpace ℝ (Fin 3))
    (Φ : EuclideanSpace ℝ (Fin 3) ≃ₗᵢ[ℝ] EuclideanSpace ℝ (Fin 3))
    (h : EuclideanSpace ℝ (Fin 2) → ℝ) : Prop :=
  ContDiff ℝ 2 h ∧ h 0 = 0 ∧ fderiv ℝ h 0 = 0 ∧
    ∃ U : Set (EuclideanSpace ℝ (Fin 2)), ∃ V : Set (EuclideanSpace ℝ (Fin 3)),
      IsOpen U ∧ (0 : EuclideanSpace ℝ (Fin 2)) ∈ U ∧ IsOpen V ∧ p ∈ V ∧
      S ∩ V = chartPoint p Φ h '' U

/-- `p` is an umbilical point of `S`: in a graph chart the Hessian is scalar. -/
def IsUmbilic (S : Set (EuclideanSpace ℝ (Fin 3))) (p : EuclideanSpace ℝ (Fin 3)) : Prop :=
  ∃ Φ h, GraphChart S p Φ h ∧ ∃ c : ℝ, ∀ u v : EuclideanSpace ℝ (Fin 2),
    iteratedFDeriv ℝ 2 h 0 ![u, v] = c * inner ℝ u v

theorem main :
    ∀ K : Set (EuclideanSpace ℝ (Fin 3)),
      IsCompact K → Convex ℝ K → (interior K).Nonempty →
      (∀ p ∈ frontier K, ∃ Φ h, GraphChart (frontier K) p Φ h) →
      ∃ p ∈ frontier K, ∃ q ∈ frontier K, p ≠ q ∧
        IsUmbilic (frontier K) p ∧ IsUmbilic (frontier K) q := by
  sorry

end OMA.S_wp_caratheodory_conjecture
