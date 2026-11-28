import Mathlib

/-!
# Isometric immersion of the hyperbolic plane into R⁴

Source: https://bookstore.ams.org/surv-130
(Q. Han and J.-X. Hong, *Isometric Embedding of Riemannian Manifolds in Euclidean Spaces*,
AMS Mathematical Surveys and Monographs 130, 2006.)
Credit: @eltociear

Source statement: does the hyperbolic plane H² (the complete simply connected surface of
constant curvature −1) admit a smooth (C^∞, or even C²) isometric immersion into Euclidean
space R⁴? Hilbert (1901): none into R³; Blanuša (1955): a smooth isometric embedding into R⁶;
Rozendorn (1960): a smooth isometric immersion into R⁵. Open for R⁴.

Formalization.
* Model of H². Up to isometry, H² is the Poincaré upper half-plane
  `U = {p : ℝ × ℝ | 0 < p.2}` with the metric `(dx² + dy²) / y²`. This model is complete,
  simply connected and of constant curvature −1, so by Killing–Hopf it is H².
* Isometric immersion. A map `f : ℝ × ℝ → EuclideanSpace ℝ (Fin 4)` that is regular on `U`
  and whose derivative preserves the metric at every point of `U`:
  `‖Df(p) v‖² = (v₁² + v₂²) / p₂²` for every tangent vector `v`. (The norm of `ℝ × ℝ` is the
  sup norm, so the Euclidean length of `v` is written out.) By polarization this is the same as
  `⟪Df(p) v, Df(p) w⟫ = ⟪v, w⟫ / p₂²`, i.e. `f` pulls the Euclidean metric back to the
  hyperbolic one. It forces `Df(p)` to be injective, so `f` is automatically an immersion.
  Injectivity of `f` is not required (an embedding would be the stronger property).
  Values of `f` off `U` are irrelevant.
* Regularity. Reading of the source: the question is asked for smooth (C^∞) maps, and the
  parenthetical (or even C²) says the question stays open for the weaker class C². We state
  the headline C^∞ question (`ContDiffOn ℝ ∞`, the smooth class, not the analytic class `ω`).
  The C² variant is the same statement with `∞` replaced by `2`. C¹ is excluded on purpose:
  Nash–Kuiper gives C¹ isometric embeddings already into R³.

The statement asserts existence: a proof answers the question yes, a disproof answers it no.
-/

namespace OMA.S_isometric_immersion_hyperbolic_plane_r4

open scoped ContDiff

/-- The upper half-plane, the underlying set of the Poincaré model of the hyperbolic plane. -/
def upperHalfPlane : Set (ℝ × ℝ) := {p | 0 < p.2}

/-- `f` is a smooth (C^∞) isometric immersion of the Poincaré upper half-plane, with metric
`(dx² + dy²) / y²`, into Euclidean `R⁴`. -/
def IsSmoothIsometricImmersion (f : ℝ × ℝ → EuclideanSpace ℝ (Fin 4)) : Prop :=
  ContDiffOn ℝ ∞ f upperHalfPlane ∧
    ∀ p ∈ upperHalfPlane, ∀ v : ℝ × ℝ,
      ‖fderiv ℝ f p v‖ ^ 2 = (v.1 ^ 2 + v.2 ^ 2) / p.2 ^ 2

/-- The hyperbolic plane admits a smooth isometric immersion into `R⁴`. -/
theorem main : ∃ f : ℝ × ℝ → EuclideanSpace ℝ (Fin 4), IsSmoothIsometricImmersion f := by
  sorry

end OMA.S_isometric_immersion_hyperbolic_plane_r4
