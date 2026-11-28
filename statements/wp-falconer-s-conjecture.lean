import Mathlib

-- Falconer's conjecture: compact sets of Hausdorff dimension greater than d/2 in ℝ^d have a
-- distance set of nonzero Lebesgue measure.
-- Source: https://en.wikipedia.org/wiki/Falconer%27s_conjecture
-- Credit: @Dugongue (agent: Claude Code, model claude-opus-5-5)

/-!
Source: if `S` is a compact set of points in `d`-dimensional Euclidean space whose Hausdorff
dimension is strictly greater than `d/2`, then the set of distances between pairs of points in `S`
has nonzero Lebesgue measure.

Conventions:
* `d`-dimensional Euclidean space is `EuclideanSpace ℝ (Fin d)`; Hausdorff dimension is
  Mathlib's `dimH` (valued in `ℝ≥0∞`); the distance set is `{|x - y| : x, y ∈ S} ⊆ ℝ`, measured by
  Lebesgue measure `volume` on `ℝ`. Including `x = y` only adds the point `0`.
* `d ≥ 2`. The Wikipedia text does not restrict `d`; its cited reference for the statement
  (Iosevich, What is ... Falconer's conjecture?, Notices AMS 66 (2019) 552-555) states the
  conjecture for `E ⊂ ℝ^d` with `d ≥ 2`, and that standard reading is used here.
-/

namespace OMA.S_wp_falconer_s_conjecture

/-- The distance set of `S`. -/
def distanceSet {d : ℕ} (S : Set (EuclideanSpace ℝ (Fin d))) : Set ℝ :=
  {r | ∃ x ∈ S, ∃ y ∈ S, dist x y = r}

/-- Falconer's distance conjecture. -/
theorem main : ∀ d : ℕ, 2 ≤ d → ∀ S : Set (EuclideanSpace ℝ (Fin d)), IsCompact S →
    (d : ENNReal) / 2 < dimH S → MeasureTheory.volume (distanceSet S) ≠ 0 := by
  sorry

end OMA.S_wp_falconer_s_conjecture
