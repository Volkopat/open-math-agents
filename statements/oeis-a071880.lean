import Mathlib

/-!
# A071880: Voronoi's conjecture on parallelohedra

Source: https://oeis.org/A071880
-- Credit: @Dugongue (agent: Claude Code, model claude-opus-5-5)

Conjecture (Voronoi, stated in A071880 as open for `n > 5`): every parallelotope in `ℝⁿ` is,
up to an affine transformation, the Voronoi cell of some lattice in `ℝⁿ`.

Conventions:
* A parallelotope (parallelohedron) is a convex polytope `P ⊆ ℝⁿ` (convex hull of a finite set,
  nonempty interior) that tiles `ℝⁿ` by translations: for some set `T` of translation vectors,
  the translates `t + P` cover `ℝⁿ` and have pairwise disjoint interiors. (Such tilings are known
  to be face-to-face lattice tilings, Venkov–McMullen.)
* A lattice is the `ℤ`-span of a basis of `ℝⁿ`; its Voronoi cell at `0` is the set of points at
  least as close to `0` as to every lattice point.
* "Up to an affine transformation": `A(P)` equals the Voronoi cell for an affine automorphism `A`.
-/

namespace OMA.S_oeis_a071880

open scoped Pointwise

/-- The Voronoi cell at `0` of the lattice spanned by the basis `b`. -/
def voronoiCell {n : ℕ} (b : Module.Basis (Fin n) ℝ (EuclideanSpace ℝ (Fin n))) :
    Set (EuclideanSpace ℝ (Fin n)) :=
  {x | ∀ v ∈ Submodule.span ℤ (Set.range b), dist x 0 ≤ dist x v}

theorem main :
    ∀ (n : ℕ) (S : Finset (EuclideanSpace ℝ (Fin n))) (T : Set (EuclideanSpace ℝ (Fin n))),
      (interior (convexHull ℝ (S : Set (EuclideanSpace ℝ (Fin n))))).Nonempty →
      (⋃ t ∈ T, (t +ᵥ convexHull ℝ (S : Set (EuclideanSpace ℝ (Fin n))))) = Set.univ →
      (∀ t ∈ T, ∀ t' ∈ T, t ≠ t' →
        Disjoint (interior (t +ᵥ convexHull ℝ (S : Set (EuclideanSpace ℝ (Fin n)))))
          (interior (t' +ᵥ convexHull ℝ (S : Set (EuclideanSpace ℝ (Fin n)))))) →
      ∃ (A : EuclideanSpace ℝ (Fin n) ≃ᵃ[ℝ] EuclideanSpace ℝ (Fin n))
        (b : Module.Basis (Fin n) ℝ (EuclideanSpace ℝ (Fin n))),
        A '' convexHull ℝ (S : Set (EuclideanSpace ℝ (Fin n))) = voronoiCell b := by
  sorry

end OMA.S_oeis_a071880
