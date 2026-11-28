import Mathlib

/-!
# Dissection into orthoschemes: is it possible for simplices of every dimension?

Source: https://en.wikipedia.org/wiki/Dissection_into_orthoschemes
-- Credit: @Dugongue (agent: Claude Code, model claude-opus-5-5)

Open problem (Hadwiger's conjecture, Wikipedia): can every simplex, in every dimension, be
dissected into finitely many orthoschemes?

Conventions:
* A `d`-simplex in `ℝ^d` is the convex hull of `d + 1` affinely independent points.
* An orthoscheme (path-simplex) is the convex hull of points `v₀, …, v_d` whose consecutive
  differences `v_{i+1} - v_i` are nonzero and pairwise orthogonal.
* A dissection of `S` into finitely many pieces: finitely many pieces whose union is `S` and whose
  interiors are pairwise disjoint.
* The source asks a yes/no question; `main` states the answer yes (Hadwiger's conjecture), and a
  disproof would answer no.
-/

namespace OMA.S_wp_dissection_into_orthoschemes_is_it_possible_for_simplices_of_every_dimension

/-- `S` is an orthoscheme in `ℝ^d`. -/
def IsOrthoscheme {d : ℕ} (S : Set (EuclideanSpace ℝ (Fin d))) : Prop :=
  ∃ v : Fin (d + 1) → EuclideanSpace ℝ (Fin d),
    (∀ i : Fin d, v i.succ - v i.castSucc ≠ 0) ∧
    (∀ i j : Fin d, i ≠ j → inner ℝ (v i.succ - v i.castSucc) (v j.succ - v j.castSucc) = 0) ∧
    S = convexHull ℝ (Set.range v)

theorem main :
    ∀ (d : ℕ) (v : Fin (d + 1) → EuclideanSpace ℝ (Fin d)), AffineIndependent ℝ v →
      ∃ (k : ℕ) (T : Fin k → Set (EuclideanSpace ℝ (Fin d))),
        (∀ i, IsOrthoscheme (T i)) ∧ (⋃ i, T i) = convexHull ℝ (Set.range v) ∧
        ∀ i j, i ≠ j → Disjoint (interior (T i)) (interior (T j)) := by
  sorry

end OMA.S_wp_dissection_into_orthoschemes_is_it_possible_for_simplices_of_every_dimension
