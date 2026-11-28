import Mathlib

/-!
# Convex bodies with constant maximal section function in odd dimensions

Source: https://mathoverflow.net/questions/70391
-- Credit: @Dugongue (agent: Claude Code, model claude-opus-5-5)

Klee asked whether a convex body in `ℝⁿ` (`n ≥ 3`) whose maximal hyperplane sections have the
same volume in every direction must be a ball. There are simple counterexamples in even
dimensions; the question is about odd `n`, e.g. `n = 3`. `main` states Klee's question for
`n = 3` with the answer yes; a counterexample in `ℝ³` would answer no.

Conventions:
* A convex body is a compact convex `K ⊆ ℝ³` with nonempty interior. The section of `K` by the
  plane `{x | ⟪u, x⟫ = t}` (`‖u‖ = 1`) has area `μH[2]` (2-dimensional Hausdorff measure); the
  maximal section function is `u ↦ sup_t μH[2](K ∩ {⟪u, ·⟫ = t})`.
* A ball is `Metric.closedBall c r`.
-/

namespace OMA.S_mo_70391

open MeasureTheory

/-- Three-dimensional Euclidean space. -/
abbrev E := EuclideanSpace ℝ (Fin 3)

/-- The maximal section area of `K` in direction `u`. -/
noncomputable def maxSection (K : Set E) (u : E) : ENNReal :=
  ⨆ t : ℝ, μH[2] (K ∩ {x | inner ℝ u x = t})

/-- A convex body in `ℝ³` with constant maximal section function is a ball. -/
theorem main : ∀ K : Set E, IsCompact K → Convex ℝ K → (interior K).Nonempty →
    (∃ c : ENNReal, ∀ u : E, ‖u‖ = 1 → maxSection K u = c) →
    ∃ (x : E) (r : ℝ), K = Metric.closedBall x r := by
  sorry

end OMA.S_mo_70391
