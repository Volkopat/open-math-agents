import Mathlib

/-!
# Plank invariant measures on convex bodies

Source: https://mathoverflow.net/questions/283370/plank-invariant-measures-on-convex-bodies
Credit: @Dugongue (agent: Claude Code, model claude-opus-5-5)

Let `K ⊂ ℝ²` be a convex body with diameter `d`. Suppose there is a measure `μ` on `K` such
that `μ(P ∩ K)` is the same for all planks `P` of some fixed width `0 < h < d` which properly
intersect `K`. Must `K` be a disk? (A disk admits such a measure, by Archimedes' hat-box theorem.)

## Encoding

* `ℝ² = EuclideanSpace ℝ (Fin 2)`. A convex body is a compact convex set with nonempty interior.
* A plank of width `h` is `{x | a ≤ ⟪u, x⟫ ≤ a + h}` with `‖u‖ = 1`; it properly intersects `K`
  when both boundary lines `⟪u, x⟫ = a` and `⟪u, x⟫ = a + h` meet `K`.
* `μ` is a finite, nonzero Borel measure with `μ Kᶜ = 0` (a measure on `K`); nonzero excludes the
  trivial zero measure.
* The question is stated with the answer yes: `K` is a closed disk.
-/

namespace OMA.S_mo_283370

open MeasureTheory

/-- The plank `{x | a ≤ ⟪u, x⟫ ≤ a + h}`. -/
def plank (u : EuclideanSpace ℝ (Fin 2)) (a h : ℝ) : Set (EuclideanSpace ℝ (Fin 2)) :=
  {x | a ≤ inner ℝ u x ∧ inner ℝ u x ≤ a + h}

/-- Both boundary lines of the plank meet `K`. -/
def ProperlyMeets (K : Set (EuclideanSpace ℝ (Fin 2))) (u : EuclideanSpace ℝ (Fin 2))
    (a h : ℝ) : Prop :=
  (∃ x ∈ K, inner ℝ u x = a) ∧ ∃ y ∈ K, inner ℝ u y = a + h

theorem main :
    ∀ (K : Set (EuclideanSpace ℝ (Fin 2))), Convex ℝ K → IsCompact K → (interior K).Nonempty →
      ∀ (h : ℝ), 0 < h → h < Metric.diam K →
      ∀ (μ : Measure (EuclideanSpace ℝ (Fin 2))), IsFiniteMeasure μ → μ ≠ 0 → μ Kᶜ = 0 →
        (∃ c, ∀ (u : EuclideanSpace ℝ (Fin 2)) (a : ℝ), ‖u‖ = 1 → ProperlyMeets K u a h →
          μ (plank u a h ∩ K) = c) →
        ∃ (z : EuclideanSpace ℝ (Fin 2)) (r : ℝ), K = Metric.closedBall z r := by
  sorry

end OMA.S_mo_283370
