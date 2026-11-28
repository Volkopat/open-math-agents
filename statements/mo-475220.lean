import Mathlib

/-!
# A generalisation of Barrow's inequality via the tangential triangle

Source: https://mathoverflow.net/questions/475220/a-generalization-of-barrows-inequality
-- Credit: @Dugongue (agent: Claude Code, model claude-opus-5-5)

Let `ABC` be a triangle, `P` a point inside it and `A₁B₁C₁` its tangential triangle. Let
`A', B', C'` be points on the sides `B₁C₁, C₁A₁, A₁B₁`. Let the internal bisectors of the angles
`∠B'PC', ∠C'PA', ∠A'PB'` meet the lines `BC, CA, AB` at `A'', B'', C''`. Conjecture:
`PA' + PB' + PC' ≥ 2 (PA'' + PB'' + PC'')`. (For `A' = A`, `B' = B`, `C' = C` this is Barrow's
inequality.) `main` states the inequality; the equality case is not included.

Conventions:
* `O` is the circumcentre. The tangential triangle has `A₁` = intersection of the tangents to the
  circumcircle at `B` and `C`, etc.; a point `X` lies on the tangent at `B` iff
  `⟪X - B, B - O⟫ = 0`. (If two tangents are parallel the hypotheses are unsatisfiable.)
* "`A'` on side `B₁C₁`" means `A'` lies on the closed segment `[B₁, C₁]`.
* `A''` lies on the line `BC` and on the internal bisector of `∠B'PC'`, expressed by
  `∠B'PA'' = ∠A''PC' = ∠B'PC' / 2` (unoriented angles).
-/

namespace OMA.S_mo_475220

open EuclideanGeometry

/-- The Euclidean plane. -/
abbrev Plane := EuclideanSpace ℝ (Fin 2)

theorem main :
    ∀ (A B C P O A₁ B₁ C₁ A' B' C' A'' B'' C'' : Plane),
      AffineIndependent ℝ ![A, B, C] →
      P ∈ interior (convexHull ℝ {A, B, C}) →
      dist O A = dist O B → dist O B = dist O C →
      inner ℝ (A₁ - B) (B - O) = 0 → inner ℝ (A₁ - C) (C - O) = 0 →
      inner ℝ (B₁ - C) (C - O) = 0 → inner ℝ (B₁ - A) (A - O) = 0 →
      inner ℝ (C₁ - A) (A - O) = 0 → inner ℝ (C₁ - B) (B - O) = 0 →
      Wbtw ℝ B₁ A' C₁ → Wbtw ℝ C₁ B' A₁ → Wbtw ℝ A₁ C' B₁ →
      A'' ∈ line[ℝ, B, C] → ∠ B' P A'' = ∠ B' P C' / 2 → ∠ A'' P C' = ∠ B' P C' / 2 →
      B'' ∈ line[ℝ, C, A] → ∠ C' P B'' = ∠ C' P A' / 2 → ∠ B'' P A' = ∠ C' P A' / 2 →
      C'' ∈ line[ℝ, A, B] → ∠ A' P C'' = ∠ A' P B' / 2 → ∠ C'' P B' = ∠ A' P B' / 2 →
      2 * (dist P A'' + dist P B'' + dist P C'') ≤ dist P A' + dist P B' + dist P C' := by
  sorry

end OMA.S_mo_475220
