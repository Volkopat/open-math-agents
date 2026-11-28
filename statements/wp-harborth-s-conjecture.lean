import Mathlib

/-!
# Harborth's conjecture

Source: https://en.wikipedia.org/wiki/Harborth's_conjecture
Credit: @matejpekar

We use finite simple graphs, as in Geelen, Guo and McKinnon, Conjecture 1.1
(https://doi.org/10.1002/jgt.20304). The planarity predicate follows the arc drawing
in `statements/wp-apex-graph.lean` by @sntntHb, using the Euclidean plane as its target.
-/

namespace OMA.S_wp_harborth_s_conjecture

abbrev Plane := EuclideanSpace ℝ (Fin 2)

/-- A plane drawing has distinct vertices and simple edge arcs whose interiors avoid
all vertices and the interiors of every other edge arc. -/
def IsPlanar {V : Type} (G : SimpleGraph V) : Prop :=
  ∃ (pos : V → Plane) (arc : G.edgeSet → C(unitInterval, Plane)),
    Function.Injective pos ∧
    (∀ e, Function.Injective (arc e)) ∧
    (∀ e, Sym2.map pos e.1 = s(arc e 0, arc e 1)) ∧
    (∀ e (t : unitInterval), (t : ℝ) ∈ Set.Ioo 0 1 → ∀ v, arc e t ≠ pos v) ∧
    (∀ e f, e ≠ f → ∀ s t : unitInterval, (s : ℝ) ∈ Set.Ioo 0 1 → (t : ℝ) ∈ Set.Ioo 0 1 →
      arc e s ≠ arc f t)

/-- In a plane straight-line drawing, edge interiors contain no vertex and are
pairwise disjoint for distinct edges. -/
def IsPlaneStraightLineDrawing {V : Type} (G : SimpleGraph V) (pos : V → Plane) : Prop :=
  Function.Injective pos ∧
    (∀ u v, G.Adj u v → ∀ w, pos w ∉ openSegment ℝ (pos u) (pos v)) ∧
    (∀ u v x y, G.Adj u v → G.Adj x y → s(u, v) ≠ s(x, y) →
      Disjoint (openSegment ℝ (pos u) (pos v)) (openSegment ℝ (pos x) (pos y)))

/-- Every finite simple planar graph has a plane straight-line drawing with integer edge lengths. -/
theorem main :
    ∀ (V : Type) [Finite V] (G : SimpleGraph V), IsPlanar G →
      ∃ pos : V → Plane, IsPlaneStraightLineDrawing G pos ∧
        ∀ u v, G.Adj u v → ∃ n : ℕ, dist (pos u) (pos v) = (n : ℝ) := by
  sorry

end OMA.S_wp_harborth_s_conjecture

