import Mathlib

/-!
# Gilbert–Pollak conjecture

Source: https://en.wikipedia.org/wiki/Gilbert–Pollak_conjecture
Credit: @dhairyajangir

The conjecture (Gilbert and Pollak, 1968): for every finite set of points in the Euclidean plane,
the Euclidean minimum spanning tree is no longer than `2 / √3` times the Steiner minimum tree.
Equivalently, in the convention of the problem list, the Steiner ratio (shortest Steiner tree over
shortest spanning tree) is `√3 / 2`: the three corners of an equilateral triangle attain this value,
so the open content is the inequality `(√3 / 2) * L(MST) ≤ L(SMT)` for all finite point sets.

Conventions:
- A tree on a finite set `V` of points is a `SimpleGraph` on `V` satisfying `IsTree`. Its edges are
  straight segments and its length is the sum of their Euclidean lengths.
- A spanning tree of `P` is a tree whose vertex set is exactly `P`.
- A Steiner tree of `P` is a tree whose vertex set is any finite set `Q` containing `P`; the points
  of `Q` outside `P` are the Steiner points.
- The statement compares trees directly: every Steiner tree `T` is matched by some spanning tree
  of length at most `(2 / √3)` times that of `T`. This says that the minimum spanning length is at
  most `2 / √3` times the minimum Steiner length, without having to assert that the latter
  minimum is attained.
- `P` is nonempty, because `IsTree` requires at least one vertex.
-/

namespace OMA.S_wp_gilbert_pollak_conjecture

/-- Total Euclidean length of a graph whose vertices are a finite set of points of the plane.
The double sum counts every edge twice, once in each direction, hence the division by two. -/
noncomputable def treeLength (V : Finset (EuclideanSpace ℝ (Fin 2))) (T : SimpleGraph V) : ℝ :=
  open Classical in (∑ u : V, ∑ v : V, if T.Adj u v then dist u.1 v.1 else 0) / 2

theorem main :
    ∀ P : Finset (EuclideanSpace ℝ (Fin 2)), P.Nonempty →
      ∀ Q : Finset (EuclideanSpace ℝ (Fin 2)), P ⊆ Q →
        ∀ T : SimpleGraph Q, T.IsTree →
          ∃ M : SimpleGraph P, M.IsTree ∧
            Real.sqrt 3 / 2 * treeLength P M ≤ treeLength Q T := by
  sorry

end OMA.S_wp_gilbert_pollak_conjecture
