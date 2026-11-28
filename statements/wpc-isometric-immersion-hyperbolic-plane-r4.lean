import Mathlib

/-!
# Isometric immersion of the hyperbolic plane into R⁴

Source: https://doi.org/10.1155/2021/2012354
Credit: @John-A-McMahon

Source statement: does the hyperbolic plane H² (the complete, simply connected surface of constant
curvature −1) admit a smooth isometric immersion into four-dimensional Euclidean space R⁴?
(Hilbert ruled out R³; Blanuša gave a smooth isometric embedding into R⁶, Rozendorn into R⁵.)

Formalization. H² is modelled, up to isometry, by the upper half-plane
`U = {p : ℝ × ℝ | 0 < p.2}` with the Poincaré metric `(dx² + dy²) / y²`; this model is complete,
simply connected and of constant curvature −1, so it is H². A smooth isometric immersion of H² into
R⁴ is then a map `f : ℝ × ℝ → EuclideanSpace ℝ (Fin 4)` that is `C^n` on `U` for every `n`
(smooth; `C^∞`, deliberately not the analytic class) and whose derivative preserves the metric at
every point of `U`: `‖Df(p) v‖² = (v₁² + v₂²) / p₂²` for all tangent vectors `v`. The metric
condition forces `Df(p)` to be injective, so such an `f` is automatically an immersion; no
injectivity of `f` is required (an embedding would be the stronger property). The statement asserts
existence; a proof answers the question yes, a disproof answers it no.
-/

namespace OMA.S_wpc_isometric_immersion_hyperbolic_plane_r4

/-- The upper half-plane, the domain of the Poincaré model of the hyperbolic plane. -/
def upperHalfPlane : Set (ℝ × ℝ) := {p | 0 < p.2}

/-- `f` is a smooth isometric immersion of the Poincaré upper half-plane into Euclidean `R⁴`. -/
def IsSmoothIsometricImmersionR4 (f : ℝ × ℝ → EuclideanSpace ℝ (Fin 4)) : Prop :=
  (∀ n : ℕ, ContDiffOn ℝ n f upperHalfPlane) ∧
  ∀ p ∈ upperHalfPlane, ∀ v : ℝ × ℝ,
    ‖fderiv ℝ f p v‖ ^ 2 = (v.1 ^ 2 + v.2 ^ 2) / p.2 ^ 2

theorem main : ∃ f : ℝ × ℝ → EuclideanSpace ℝ (Fin 4), IsSmoothIsometricImmersionR4 f := by
  sorry

end OMA.S_wpc_isometric_immersion_hyperbolic_plane_r4
