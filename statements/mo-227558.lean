import Mathlib

/-!
# Octahedron and a system of trigonometric equations

Source: https://mathoverflow.net/questions/227558
Asked by MathOverflow user Ma Na.

For angles `θ_1, ..., θ_6` and `φ_1, ..., φ_6` the asker wants to prove that the eight
equations
* `∑ cos (2 θ_k) (cos (2 φ_k) - 1) = 0`,
* `∑ sin (2 θ_k) (cos (2 φ_k) - 1) = 0`,
* `∑ cos φ_k = 0`,
* `∑ cos (2 φ_k) = -2`,
* `∑ cos θ_k sin φ_k = 0`,
* `∑ sin θ_k sin φ_k = 0`,
* `∑ cos θ_k sin (2 φ_k) = 0`,
* `∑ sin θ_k sin (2 φ_k) = 0`
(all sums over `k = 1, ..., 6`) hold if and only if the six points
`(cos θ_k sin φ_k, sin θ_k sin φ_k, cos φ_k)` are the vertices of a regular octahedron.

Translation choices.
* The indices run over `Fin 6`; the point with spherical coordinates `(θ, φ)` is
  `sphPoint θ φ` in `EuclideanSpace ℝ (Fin 3)`; it lies on the unit sphere.
* A regular octahedron whose vertices lie on the unit sphere centred at the origin has
  vertices `± u 0, ± u 1, ± u 2` for an orthonormal family `u`. The six points form the
  vertices of a regular octahedron when the set of the six points is exactly such a set
  (`IsRegularOctahedron`); in particular the six points are then distinct.
* `main` is the stated equivalence, for all angles.
-/

namespace OMA.S_mo_227558

open Real

/-- The point of the unit sphere with spherical coordinates `θ` (longitude) and `φ`
(polar angle). -/
noncomputable def sphPoint (θ φ : ℝ) : EuclideanSpace ℝ (Fin 3) :=
  WithLp.toLp 2 ![cos θ * sin φ, sin θ * sin φ, cos φ]

/-- The six points are exactly the vertices `± u i` of a regular octahedron inscribed in
the unit sphere. -/
def IsRegularOctahedron (v : Fin 6 → EuclideanSpace ℝ (Fin 3)) : Prop :=
  ∃ u : Fin 3 → EuclideanSpace ℝ (Fin 3), Orthonormal ℝ u ∧
    Set.range v = {u 0, -u 0, u 1, -u 1, u 2, -u 2}

theorem main :
    ∀ θ φ : Fin 6 → ℝ,
      ((∑ k, cos (2 * θ k) * (cos (2 * φ k) - 1) = 0) ∧
        (∑ k, sin (2 * θ k) * (cos (2 * φ k) - 1) = 0) ∧
        (∑ k, cos (φ k) = 0) ∧
        (∑ k, cos (2 * φ k) = -2) ∧
        (∑ k, cos (θ k) * sin (φ k) = 0) ∧
        (∑ k, sin (θ k) * sin (φ k) = 0) ∧
        (∑ k, cos (θ k) * sin (2 * φ k) = 0) ∧
        (∑ k, sin (θ k) * sin (2 * φ k) = 0)) ↔
      IsRegularOctahedron (fun k => sphPoint (θ k) (φ k)) := by
  sorry

end OMA.S_mo_227558
