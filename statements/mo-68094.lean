import Mathlib

namespace OMA.S_mo_68094

open scoped BigOperators ContDiff Manifold
open Manifold

abbrev Space (n : ℕ) := EuclideanSpace ℝ (Fin n)
abbrev Sphere (n : ℕ) := Metric.sphere (0 : Space (n + 1)) 1

/-- The normal component of an embedded coordinate patch's second derivative. -/
noncomputable def secondFundamentalForm {n e : ℕ} (F : Space n → Space e)
    (z u v : Space n) : Space e :=
  let tangent := LinearMap.range (fderiv ℝ F z).toLinearMap
  let second := fderiv ℝ (fun w => fderiv ℝ F w v) z u
  second - tangent.starProjection second

/-- Ricci curvature of the induced metric is zero, as computed by tracing
the Gauss equation over an orthonormal tangent frame. -/
def IsRicciFlat {n e : ℕ} (embed : Sphere n → Space e) : Prop :=
  ∀ x : Sphere n,
    let chart := chartAt (Space n) x
    let F := embed ∘ chart.symm
    let B := secondFundamentalForm F (chart x)
    ∀ frame : Fin n → Space n,
      Orthonormal ℝ (fun i => fderiv ℝ F (chart x) (frame i)) →
      ∀ u : Space n,
        (∑ i : Fin n,
          (inner ℝ (B (frame i) (frame i)) (B u u) - ‖B (frame i) u‖ ^ 2)) = 0

/-- Does a standard sphere of dimension greater than four carry a smooth
Ricci-flat Riemannian metric? -/
theorem main :
    ∃ (n e : ℕ) (embed : Sphere n → Space e),
      4 < n ∧
      IsSmoothEmbedding (𝓘(ℝ, Space n)) (𝓘(ℝ, Space e)) ∞ embed ∧
      IsRicciFlat embed := by
  sorry

end OMA.S_mo_68094
