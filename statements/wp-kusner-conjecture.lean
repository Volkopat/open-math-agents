import Mathlib

-- Kusner conjecture (p = 1 case): at most 2d points can be equidistant in L^1 spaces
-- Source: https://en.wikipedia.org/wiki/Equilateral_dimension (redirect target of Kusner_conjecture)
-- Credit: @Dugongue (agent: Claude Code, model claude-opus-5-5)

/-!
The source: the equilateral dimension of `d`-dimensional space with the Manhattan distance
(`L^1` norm) is conjectured to be exactly `2d`. The lower bound `2d` is attained by the vertices of
the cross polytope, so the open content is the upper bound stated here: every set of pairwise
equidistant points in `ℝ^d` with the `L^1` distance has at most `2d` points.

Conventions:
* The `L^1` distance is written out as `∑ i, |x i - y i|` (Mathlib's default norm on `Fin d → ℝ`
  is the sup norm, so it is not used).
* Equidistant: all distances between distinct points of the set are equal to one common value.
* Dimension `d ≥ 1` (in dimension `0` the space is a single point).
* Only the `p = 1` part of Kusner's conjecture is stated (the source lists the `p > 2` part as a
  related suggestion; the catalogue entry is the `L^1` statement).
-/

namespace OMA.S_wp_kusner_conjecture

/-- The `L^1` (Manhattan) distance on `ℝ^d`. -/
def l1dist {d : ℕ} (x y : Fin d → ℝ) : ℝ := ∑ i, |x i - y i|

/-- Kusner's conjecture for `L^1`: an equilateral set in `(ℝ^d, L^1)` has at most `2d` points. -/
theorem main : ∀ d : ℕ, 1 ≤ d → ∀ S : Finset (Fin d → ℝ),
    (∃ r : ℝ, ∀ x ∈ S, ∀ y ∈ S, x ≠ y → l1dist x y = r) → S.card ≤ 2 * d := by
  sorry

end OMA.S_wp_kusner_conjecture
