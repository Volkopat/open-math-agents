import Mathlib

/-!
# Danzer set

Source: https://en.wikipedia.org/wiki/Danzer_set
Credit: @shc261392

A Danzer set in `d`-dimensional Euclidean space is a set of points that meets every convex body
of volume one. Danzer asked whether a Danzer set can have bounded density, i.e. growth rate
`O(r^d)`: at most `C r^d` points within distance `r` of the origin.

Reading used here (the affirmative form of the question):
* The dimension is `d ≥ 2`; in dimension one the integers are a Danzer set of bounded density.
  The statement asks for a bounded-density Danzer set in every dimension `d ≥ 2`.
* A convex body of volume one is a compact convex `K ⊆ ℝ^d` with `volume K = 1`.
* Bounded density: there is `C` with `|S ∩ ball(0, r)| ≤ C r^d` for all `r ≥ 1` (the
  intersection being finite).
-/

namespace OMA.S_wp_danzer_set

open MeasureTheory

theorem main :
    ∀ d : ℕ, 2 ≤ d → ∃ S : Set (EuclideanSpace ℝ (Fin d)),
      (∀ K : Set (EuclideanSpace ℝ (Fin d)), Convex ℝ K → IsCompact K → volume K = 1 →
        (S ∩ K).Nonempty) ∧
      ∃ C : ℝ, ∀ r : ℝ, 1 ≤ r →
        (S ∩ Metric.ball 0 r).Finite ∧ ((S ∩ Metric.ball 0 r).ncard : ℝ) ≤ C * r ^ d := by
  sorry

end OMA.S_wp_danzer_set
