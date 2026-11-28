import Mathlib

/-!
# Universal point sets for planar graphs

Source: https://www.openproblemgarden.org/op/small_universal_point_sets_for_planar_graphs
Credit: @pyaf

A set `P ⊆ ℝ²` is `n`-universal if every `n`-vertex planar graph can be drawn in the plane so that
each vertex maps to a distinct point of `P` and all edges are (non-intersecting) straight line
segments. Question: does there exist an `n`-universal set of size `O(n)`?

## Encoding

* Graphs are finite simple graphs; an `n`-vertex graph is a `SimpleGraph (Fin n)`.
* A graph is planar if it has a plane drawing with arcs (`IsPlanar`, the same definition as in
  `wp-apex-graph`).
* A straight-line drawing on `P` places the vertices at distinct points of `P`; each edge is the
  segment between its endpoints, and the open segment of an edge contains no vertex and does not
  meet the open segment of any other edge (so distinct edges meet at most in a common endpoint).
* `O(n)`: there is a constant `C` with an `n`-universal set of at most `C * n` points for all
  sufficiently large `n`.
* The source asks a yes/no question; `main` states the answer yes, and a disproof would answer no.
-/

namespace OMA.S_opg_small_universal_point_sets_for_planar_graphs

open SimpleGraph Filter

/-- `G` has a plane drawing: vertices at distinct points, edges as arcs joining their endpoints,
with arc interiors avoiding all vertices and the interiors of all other arcs. -/
def IsPlanar {V : Type} (G : SimpleGraph V) : Prop :=
  ∃ (pos : V → ℝ × ℝ) (arc : G.edgeSet → C(unitInterval, ℝ × ℝ)),
    Function.Injective pos ∧
    (∀ e, Function.Injective (arc e)) ∧
    (∀ e, Sym2.map pos e.1 = s(arc e 0, arc e 1)) ∧
    (∀ e (t : unitInterval), (t : ℝ) ∈ Set.Ioo 0 1 → ∀ v, arc e t ≠ pos v) ∧
    (∀ e f, e ≠ f → ∀ s t : unitInterval, (s : ℝ) ∈ Set.Ioo 0 1 → (t : ℝ) ∈ Set.Ioo 0 1 →
      arc e s ≠ arc f t)

/-- `G` has a straight-line plane drawing with all vertices at distinct points of `P`. -/
def HasStraightLineDrawingOn {V : Type} (G : SimpleGraph V) (P : Set (ℝ × ℝ)) : Prop :=
  ∃ pos : V → ℝ × ℝ,
    Function.Injective pos ∧ (∀ v, pos v ∈ P) ∧
    (∀ u v, G.Adj u v → ∀ w, pos w ∉ openSegment ℝ (pos u) (pos v)) ∧
    (∀ u v x y, G.Adj u v → G.Adj x y → s(u, v) ≠ s(x, y) →
      Disjoint (openSegment ℝ (pos u) (pos v)) (openSegment ℝ (pos x) (pos y)))

/-- `P` is `n`-universal: every planar graph on `n` vertices has a straight-line drawing on `P`. -/
def IsUniversal (n : ℕ) (P : Set (ℝ × ℝ)) : Prop :=
  ∀ G : SimpleGraph (Fin n), IsPlanar G → HasStraightLineDrawingOn G P

/-- There are `n`-universal point sets of size `O(n)`. -/
theorem main :
    ∃ C : ℝ, ∀ᶠ n : ℕ in atTop, ∃ P : Finset (ℝ × ℝ), (P.card : ℝ) ≤ C * n ∧ IsUniversal n P := by
  sorry

end OMA.S_opg_small_universal_point_sets_for_planar_graphs
