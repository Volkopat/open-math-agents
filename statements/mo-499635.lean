import Mathlib

/-!
# The Gaussian center of mass of a triangle determines any single vertex

Source: https://mathoverflow.net/questions/499635
Credit: @tox5tox5

State the problem EXACTLY as the source states it: same quantifiers, same ranges, no simplification.
Do not prove it here: the theorem body stays `sorry`. A person reviews the translation before merging.

The question (MathOverflow 499635, Aug 2025): consider a triangle `Δ` in the plane with vertices
`A, B, C` and a second triangle `Δ'` differing only in one vertex (`C'` instead of `C`). With
`γ(x) = (2π)^{-1/2} e^{-‖x‖²/2}` the normal density, the centers of Gaussian mass restricted to
the triangles are `e = ∫_Δ x γ(x) dx / ∫_Δ γ(x) dx` and `e' = ∫_{Δ'} x γ(x) dx / ∫_{Δ'} γ(x) dx`.
"I want to show that `C' ≠ C` implies `e' ≠ e`." In a comment the asker confirms that `ABC` and
`ABC'` can be assumed to have positive area. The asker adds that whether the triangle contains the
origin "hopefully doesn't matter" (one may assume it does), and that the real goal is
`n`-simplices in `ℝⁿ`; this file states the planar question without the optional origin
assumption. The page has no answer.

Modelling choices:
* The plane is `EuclideanSpace ℝ (Fin 2)` with Lebesgue measure `volume`; a triangle is the convex
  hull of its three vertices, and "positive area" is affine independence of the vertices.
* The normalizing constant of `γ` cancels in `e`, so `γ` is taken to be `exp (-‖x‖² / 2)`
  without it (any positive multiple gives the same centers).
-/

namespace OMA.S_mo_499635

open MeasureTheory

/-- The (unnormalized) standard Gaussian density on the plane. -/
noncomputable def γ (x : EuclideanSpace ℝ (Fin 2)) : ℝ := Real.exp (-‖x‖ ^ 2 / 2)

/-- The center of Gaussian mass of the triangle with vertices `A`, `B`, `C`. -/
noncomputable def center (A B C : EuclideanSpace ℝ (Fin 2)) : EuclideanSpace ℝ (Fin 2) :=
  (∫ x in convexHull ℝ {A, B, C}, γ x) ⁻¹ • ∫ x in convexHull ℝ {A, B, C}, γ x • x

/-- **MathOverflow 499635.** If `ABC` and `ABC'` are nondegenerate triangles and `C' ≠ C`, their
Gaussian centers of mass differ. -/
theorem main :
    ∀ A B C C' : EuclideanSpace ℝ (Fin 2),
      AffineIndependent ℝ ![A, B, C] → AffineIndependent ℝ ![A, B, C'] → C' ≠ C →
        center A B C' ≠ center A B C := by
  sorry

end OMA.S_mo_499635
