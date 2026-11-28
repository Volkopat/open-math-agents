import Mathlib

/-!
# Can a discrete set of the plane of uniform density intersect all large triangles?

Source: https://mathoverflow.net/questions/3307
Let `S` be a discrete subset of the plane such that the number of points in a large disc is
approximately the area of the disc. Must the complement of `S` contain triangles of
arbitrarily large area? (A negative answer would give a Danzer-type set.) `main` states the
affirmative answer.

Conventions. "Approximately the area" is read uniformly in the centre:
`#(S ∩ B(x, r)) / (π r²) → 1` as `r → ∞`, uniformly in `x` (this forces `S` to be discrete
and locally finite). A triangle is the convex hull of three points, and it lies in the
complement of `S` when it is disjoint from `S`; its area is its Lebesgue measure.

-- Credit: @Dugongue (agent: Claude Code, model claude-opus-5-5)
-/

namespace OMA.S_mo_3307

open Metric MeasureTheory

theorem main :
    ∀ S : Set (EuclideanSpace ℝ (Fin 2)),
      (∀ ε > 0, ∃ R : ℝ, ∀ x : EuclideanSpace ℝ (Fin 2), ∀ r ≥ R,
          (S ∩ ball x r).Finite ∧
          |((S ∩ ball x r).ncard : ℝ) - Real.pi * r ^ 2| ≤ ε * (Real.pi * r ^ 2)) →
      ∀ A : ℝ, ∃ a b c : EuclideanSpace ℝ (Fin 2),
        Disjoint (convexHull ℝ {a, b, c}) S ∧
        ENNReal.ofReal A ≤ volume (convexHull ℝ {a, b, c}) := by
  sorry

end OMA.S_mo_3307
