import Mathlib

/-!
# Effective radius of a maximal section of a convex set

Source: https://mathoverflow.net/questions/358940
-- Credit: @Dugongue (agent: Claude Code, model claude-opus-5-5)

The effective radius `er(A)` of an `n`-dimensional solid `A` is the radius of the `n`-ball with
the same volume. Question (a): if `A ⊆ ℝⁿ` is convex and `H` is a hyperplane such that
`B = A ∩ H` has maximal `(n-1)`-volume, is `er(B) ≥ er(A)` (with `er(B)` computed in dimension
`n - 1`)? `main` states question (a) with the answer yes; the source's question (b), about
sections of maximal boundary measure, is a separate statement.

Conventions:
* `A` is a convex body: compact, convex, nonempty interior, in `ℝⁿ`, `n ≥ 2`. Hyperplanes are
  `{x | ⟪u, x⟫ = t}` with `‖u‖ = 1`. The `(n-1)`-volume of a section is `μH[n-1]` (Mathlib's
  Hausdorff measure, which agrees with Lebesgue measure on hyperplanes).
* `er_m(v) = (v / ωₘ)^(1/m)` with `ωₘ` the volume of the unit ball of `ℝᵐ`.
-/

namespace OMA.S_mo_358940

open MeasureTheory

/-- Volume of the unit ball of `ℝᵐ`. -/
noncomputable def omega (m : ℕ) : ℝ :=
  (volume (Metric.ball (0 : EuclideanSpace ℝ (Fin m)) 1)).toReal

/-- Effective radius of an `m`-dimensional volume `v`. -/
noncomputable def er (m : ℕ) (v : ℝ) : ℝ := (v / omega m) ^ ((1 : ℝ) / m)

/-- The `(n-1)`-volume of the section of `A` by `{⟪u, ·⟫ = t}`. -/
noncomputable def sec {n : ℕ} (A : Set (EuclideanSpace ℝ (Fin n))) (u : EuclideanSpace ℝ (Fin n))
    (t : ℝ) : ℝ :=
  (μH[(n : ℝ) - 1] (A ∩ {x | inner ℝ u x = t})).toReal

/-- Question (a): a maximal-volume hyperplane section has effective radius `≥ er(A)`. -/
theorem main : ∀ (n : ℕ) (A : Set (EuclideanSpace ℝ (Fin n))), 2 ≤ n →
    IsCompact A → Convex ℝ A → (interior A).Nonempty →
    ∀ (u : EuclideanSpace ℝ (Fin n)) (t : ℝ), ‖u‖ = 1 →
      (∀ (u' : EuclideanSpace ℝ (Fin n)) (t' : ℝ), ‖u'‖ = 1 → sec A u' t' ≤ sec A u t) →
      er n (volume A).toReal ≤ er (n - 1) (sec A u t) := by
  sorry

end OMA.S_mo_358940
