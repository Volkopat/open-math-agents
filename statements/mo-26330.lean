import Mathlib

/-!
# Dissecting trapezoids into triangles of equal area (Stein's conjecture)

Source: https://mathoverflow.net/questions/26330 (asked by Monsky)
Let `T` be a trapezoid whose parallel sides have ratio `r`. Stein conjectured, and the
question asks, whether `T` has no dissection into triangles of equal area whenever the
algebraic number `r` has a `ℚ`-conjugate outside the open right half-plane. `main` states
Stein's conjecture.

Conventions. Equidissectibility is invariant under affine maps, and every trapezoid with
side ratio `r` is an affine image of `T r = conv{(0,0), (1,0), (0,1), (r,1)}`. A dissection
into `n ≥ 1` triangles of equal area is a family of `n` triangles (convex hulls of three
points) with pairwise disjoint interiors, union `T r`, and equal Lebesgue measure. The
conjugates of `r` are the complex roots of its minimal polynomial over `ℚ`.

-- Credit: @Dugongue (agent: Claude Code, model claude-opus-5-5)
-/

namespace OMA.S_mo_26330

open MeasureTheory Polynomial

/-- The point `(x, y)` of the plane. -/
noncomputable def pt (x y : ℝ) : EuclideanSpace ℝ (Fin 2) :=
  x • EuclideanSpace.single 0 1 + y • EuclideanSpace.single 1 1

/-- The model trapezoid with parallel sides `1` and `r`. -/
noncomputable def T (r : ℝ) : Set (EuclideanSpace ℝ (Fin 2)) :=
  convexHull ℝ {pt 0 0, pt 1 0, pt 0 1, pt r 1}

/-- `S` is dissected into `n ≥ 1` triangles of equal area. -/
def Equidissectible (S : Set (EuclideanSpace ℝ (Fin 2))) : Prop :=
  ∃ (n : ℕ) (v : Fin n → Fin 3 → EuclideanSpace ℝ (Fin 2)), 1 ≤ n ∧
    (⋃ i, convexHull ℝ (Set.range (v i))) = S ∧
    (∀ i j, i ≠ j → Disjoint (interior (convexHull ℝ (Set.range (v i))))
      (interior (convexHull ℝ (Set.range (v j))))) ∧
    ∀ i j, volume (convexHull ℝ (Set.range (v i))) = volume (convexHull ℝ (Set.range (v j)))

theorem main :
    ∀ r : ℝ, 0 < r → IsAlgebraic ℚ r →
      (∃ z : ℂ, aeval z (minpoly ℚ r) = 0 ∧ z.re ≤ 0) →
      ¬ Equidissectible (T r) := by
  sorry

end OMA.S_mo_26330
