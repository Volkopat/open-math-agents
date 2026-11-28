import Mathlib

/-!
# Cube-Simplex conjecture

Source: https://www.openproblemgarden.org/op/cube_simplex_conjecture
Credit: @Dugongue (agent: Claude Code, model claude-opus-5-5)

Conjecture (Kalai): for every positive integer `k` there is an integer `d` such that every
polytope of dimension at least `d` has a `k`-dimensional face which is either a simplex or is
combinatorially isomorphic to the `k`-dimensional cube.

## Encoding

* A (convex) polytope is the convex hull of a finite set of points of `ℝⁿ`
  (`EuclideanSpace ℝ (Fin n)`); `n` is arbitrary. The dimension of a convex set is the dimension
  of its affine hull, i.e. `Module.finrank ℝ (vectorSpan ℝ P)`.
* The faces of a polytope `P` are its nonempty exposed faces (Mathlib's `IsExposed`); for
  polytopes faces and exposed faces coincide. `P` itself is a face.
* A `k`-dimensional face `F` is a simplex when it has exactly `k + 1` extreme points (vertices).
* "Combinatorially isomorphic" means that the posets of nonempty faces, ordered by inclusion,
  are order-isomorphic. The `k`-cube is `[0, 1]ᵏ ⊆ ℝᵏ`.
-/

namespace OMA.S_opg_cube_simplex_conjecture

/-- The dimension of a subset of `ℝⁿ`: the dimension of its affine hull. -/
noncomputable def dim {n : ℕ} (A : Set (EuclideanSpace ℝ (Fin n))) : ℕ :=
  Module.finrank ℝ (vectorSpan ℝ A)

/-- The poset (under inclusion) of nonempty faces of a convex set `A`. -/
def Faces {n : ℕ} (A : Set (EuclideanSpace ℝ (Fin n))) : Type :=
  {F : Set (EuclideanSpace ℝ (Fin n)) // F.Nonempty ∧ IsExposed ℝ A F}

instance {n : ℕ} (A : Set (EuclideanSpace ℝ (Fin n))) : PartialOrder (Faces A) :=
  Subtype.partialOrder _

/-- The `k`-dimensional unit cube `[0, 1]ᵏ`. -/
def cube (k : ℕ) : Set (EuclideanSpace ℝ (Fin k)) :=
  {x | ∀ i, x i ∈ Set.Icc (0 : ℝ) 1}

theorem main :
    ∀ k : ℕ, 0 < k → ∃ d : ℕ, ∀ (n : ℕ) (S : Finset (EuclideanSpace ℝ (Fin n))),
      d ≤ dim (convexHull ℝ (S : Set (EuclideanSpace ℝ (Fin n)))) →
        ∃ F : Set (EuclideanSpace ℝ (Fin n)),
          F.Nonempty ∧ IsExposed ℝ (convexHull ℝ (S : Set (EuclideanSpace ℝ (Fin n)))) F ∧
          dim F = k ∧
          ((Set.extremePoints ℝ F).ncard = k + 1 ∨ Nonempty (Faces F ≃o Faces (cube k))) := by
  sorry

end OMA.S_opg_cube_simplex_conjecture
