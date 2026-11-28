import Mathlib

/-!
# Universal point sets of subquadratic size for planar graphs

Source: https://en.wikipedia.org/wiki/Universal_point_set
Does every `n` admit a universal point set for `n`-vertex planar graphs of size `o(n²)`, i.e.
a set of points in the plane such that every `n`-vertex planar graph has a straight-line
plane drawing with all vertices at points of the set? (Known: `O(n²)` points suffice.)
`main` states the affirmative answer.

Conventions. Graphs are simple graphs on `Fin n`. A straight-line plane drawing places the
vertices at distinct points so that two distinct edge segments meet only in common endpoints; by
Fáry's theorem a graph is planar exactly when it has one.

-- Credit: @Dugongue (agent: Claude Code, model claude-opus-5-5)
-/

namespace OMA.S_wp_universal_point_sets_of_subquadratic_size_for_planar_graphs

open Filter Asymptotics

/-- `pos` is a straight-line plane drawing of `G`. -/
def IsStraightLineDrawing {V : Type*} (G : SimpleGraph V)
    (pos : V → EuclideanSpace ℝ (Fin 2)) : Prop :=
  Function.Injective pos ∧
    ∀ u v x y : V, G.Adj u v → G.Adj x y → s(u, v) ≠ s(x, y) →
      segment ℝ (pos u) (pos v) ∩ segment ℝ (pos x) (pos y) ⊆
        pos '' (({u, v} : Set V) ∩ {x, y})

theorem main :
    ∃ f : ℕ → ℕ, (fun n => (f n : ℝ)) =o[atTop] (fun n => (n : ℝ) ^ 2) ∧
      ∀ n : ℕ, ∃ P : Finset (EuclideanSpace ℝ (Fin 2)), P.card ≤ f n ∧
        ∀ G : SimpleGraph (Fin n), (∃ pos, IsStraightLineDrawing G pos) →
          ∃ pos, IsStraightLineDrawing G pos ∧ ∀ v, pos v ∈ P := by
  sorry

end OMA.S_wp_universal_point_sets_of_subquadratic_size_for_planar_graphs
