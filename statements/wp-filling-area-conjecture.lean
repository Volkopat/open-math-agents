import Mathlib

/-!
# Filling area conjecture

Source: https://en.wikipedia.org/wiki/Filling_area_conjecture
Credit: @eltociear

Gromov's filling area conjecture (Gromov, *Filling Riemannian manifolds*, J. Diff. Geom. 18
(1983), p. 13), as Wikipedia states it:

> The hemisphere has minimum area among the orientable compact Riemannian surfaces that fill
> isometrically their boundary curve, of given length.

Here a compact surface `M` *fills* a closed curve `C` when its boundary `∂M` is `C`, and the filling
is *isometric* when for all `x, y ∈ C` the intrinsic distance along `M` equals the intrinsic
distance along `C` (no shortcuts). The hemisphere filling a curve of length `ℓ` has area
`ℓ² / (2π)` (for `ℓ = 2π` it is the unit hemisphere, area `2π`), so the conjecture says
`ℓ² / (2π) ≤ Area M` for every such filling.

## Encoding

Mathlib has no Riemannian surfaces with boundary and no Riemannian area. As the source itself
notes, the problem can equivalently be posed for surfaces sitting in Euclidean space. We use smooth
compact embedded surfaces with boundary in `ℝᴺ`, for every `N`. They have the induced metric, and
by Nash's smooth isometric embedding theorem every compact Riemannian surface with boundary arises
this way for some `N`. So quantifying over all `N` is the same as quantifying over abstract
Riemannian surfaces.

* A *chart* of `M ⊆ ℝᴺ` is a smooth map `φ` defined on an open set `W ⊆ ℝ²` with injective
  differential at every point of `W ∩ H`, where `H = {u | 0 ≤ u 1}` is the closed upper half-plane.
  `φ` maps `W ∩ H` homeomorphically onto a relatively open piece `M ∩ U` of `M`. (This is the
  usual definition of an embedded smooth surface with boundary; charts with `W ⊆ {u 1 > 0}` give
  the interior points.)
* `∂M` is the set of points that are the image of some `u` with `u 1 = 0` under some chart.
  By invariance of domain this does not depend on the chart.
* Orientable: an atlas of charts whose transition maps preserve orientation. If `Dψ = Dφ ∘ A` on
  the common tangent plane, the Gram-type matrix `⟨Dφ eᵢ, Dψ eⱼ⟩` equals `G A` with `G` positive
  definite, so its determinant has the sign of `det A`.
* `∂M` is the boundary curve: we ask it to be connected. A compact smooth 1-manifold that is
  connected and nonempty is a circle, so this matches «fills a closed curve». Extra closed
  components of `M` away from the boundary only add area, so `M` need not be connected.
* Intrinsic distance `d_S(x, y)` on a set `S`: the infimum of the lengths (`eVariationOn`) of
  continuous curves in `S` from `x` to `y`. For a smooth embedded surface or curve this is the
  Riemannian distance of the induced metric.
* Length and area are Hausdorff measures. Mathlib's `μH[d]` is not normalized. For a smooth
  curve, `μH[1]` is its length (the normalizing constant is `1` in dimension 1). In dimension 2
  the Riemannian area is `(π / 4) · μH[2]`: the unnormalized measure of the unit disk is `4`.

The statement is the inequality. That the hemisphere is an admissible filling attaining it is
classical and stated in the source.
-/

open MeasureTheory Set
open scoped ContDiff ENNReal

namespace OMA.S_wp_filling_area_conjecture

/-- The plane `ℝ²` in which charts are defined. -/
abbrev Plane := EuclideanSpace ℝ (Fin 2)

/-- The closed upper half-plane `{u | 0 ≤ u 1}`. -/
def upperHalf : Set Plane := {u | 0 ≤ u 1}

/-- `φ : W → ℝᴺ` is a smooth chart of `M`: smooth on the open set `W`, an immersion on `W ∩ H`,
and a homeomorphism from `W ∩ H` onto a relatively open subset `M ∩ U` of `M`. -/
def IsChart {N : ℕ} (M : Set (EuclideanSpace ℝ (Fin N))) (W : Set Plane)
    (φ : Plane → EuclideanSpace ℝ (Fin N)) : Prop :=
  IsOpen W ∧ ContDiffOn ℝ ∞ φ W ∧
    (∀ u ∈ W ∩ upperHalf, Function.Injective (fderiv ℝ φ u)) ∧
    InjOn φ (W ∩ upperHalf) ∧
    Topology.IsEmbedding ((W ∩ upperHalf).restrict φ) ∧
    ∃ U : Set (EuclideanSpace ℝ (Fin N)), IsOpen U ∧ φ '' (W ∩ upperHalf) = M ∩ U

/-- `M` is a smooth embedded surface with (possibly empty) boundary in `ℝᴺ`. -/
def IsSurfaceWithBoundary {N : ℕ} (M : Set (EuclideanSpace ℝ (Fin N))) : Prop :=
  ∀ p ∈ M, ∃ W φ, IsChart M W φ ∧ p ∈ φ '' (W ∩ upperHalf)

/-- The boundary `∂M`: images of points of the edge `{u 1 = 0}` under charts. -/
def boundary {N : ℕ} (M : Set (EuclideanSpace ℝ (Fin N))) : Set (EuclideanSpace ℝ (Fin N)) :=
  {p | ∃ W φ, IsChart M W φ ∧ ∃ u ∈ W, u 1 = 0 ∧ φ u = p}

/-- `M` is orientable: it has an atlas whose transition maps preserve orientation. -/
def IsOrientable {N : ℕ} (M : Set (EuclideanSpace ℝ (Fin N))) : Prop :=
  ∃ A : Set (Set Plane × (Plane → EuclideanSpace ℝ (Fin N))),
    (∀ c ∈ A, IsChart M c.1 c.2) ∧
    (∀ p ∈ M, ∃ c ∈ A, p ∈ c.2 '' (c.1 ∩ upperHalf)) ∧
    ∀ c ∈ A, ∀ c' ∈ A, ∀ u ∈ c.1 ∩ upperHalf, ∀ v ∈ c'.1 ∩ upperHalf, c.2 u = c'.2 v →
      0 < (Matrix.of fun i j : Fin 2 =>
        inner ℝ (fderiv ℝ c.2 u (EuclideanSpace.single i 1))
          (fderiv ℝ c'.2 v (EuclideanSpace.single j 1))).det

/-- Intrinsic distance in `S`: infimum of the lengths of continuous curves in `S` from `x` to `y`
(`⊤` if there is none). -/
noncomputable def intrinsicDist {N : ℕ} (S : Set (EuclideanSpace ℝ (Fin N)))
    (x y : EuclideanSpace ℝ (Fin N)) : ℝ≥0∞ :=
  ⨅ (γ : ℝ → EuclideanSpace ℝ (Fin N)) (_ : ContinuousOn γ (Icc 0 1))
    (_ : MapsTo γ (Icc 0 1) S) (_ : γ 0 = x) (_ : γ 1 = y), eVariationOn γ (Icc 0 1)

/-- `M` fills its boundary curve isometrically: along `M`, boundary points are no closer than
along `∂M`. -/
def IsIsometricFilling {N : ℕ} (M : Set (EuclideanSpace ℝ (Fin N))) : Prop :=
  ∀ x ∈ boundary M, ∀ y ∈ boundary M, intrinsicDist M x y = intrinsicDist (boundary M) x y

/-- **Gromov's filling area conjecture.** Take an orientable compact smooth surface `M ⊆ ℝᴺ`
whose boundary is a single closed curve, of length `ℓ = μH[1] ∂M`, and which fills that curve
isometrically. Then its area `(π / 4) · μH[2] M` is at least `ℓ² / (2π)`, the area of the
hemisphere filling a curve of the same length. -/
theorem main :
    ∀ (N : ℕ) (M : Set (EuclideanSpace ℝ (Fin N))),
      IsCompact M → IsSurfaceWithBoundary M → IsOrientable M →
      IsConnected (boundary M) → IsIsometricFilling M →
      (μH[1] (boundary M)) ^ 2 ≤
        ENNReal.ofReal (2 * Real.pi) * (ENNReal.ofReal (Real.pi / 4) * μH[2] M) := by
  sorry

end OMA.S_wp_filling_area_conjecture
