import Mathlib

/-!
# Large acyclic induced subdigraph in a planar oriented graph

Source: https://www.openproblemgarden.org/op/large_acyclic_induced_subdigraph_in_a_planar_oriented_graph
Credit: @pyaf

Conjecture (Harutyunyan): every planar oriented graph `D` has an acyclic induced subdigraph of
order at least `(3/5) |V(D)|`.

Conventions:
- An oriented graph is a finite Mathlib `Digraph V` with no pair of opposite arcs, hence no
  loops (`IsOriented`, reused verbatim from
  `statements/opg-seymours-second-neighbourhood-conjecture.lean`). It is planar if its
  underlying simple graph `SimpleGraph.fromRel D.Adj` (`u ~ v` iff `u ≠ v` and `u → v` or
  `v → u`) is planar.
- A graph is planar if it has a plane drawing: distinct points of `ℝ²` for the vertices and,
  for every edge, an arc (a continuous injective image of `[0, 1]`) joining its endpoints,
  whose interior meets no vertex and no other edge's interior (`IsPlanar`, reused verbatim from
  `statements/wp-apex-graph.lean`).
- The subdigraph induced by `X` is acyclic if it has no directed cycle: no vertex of `X` reaches
  itself by a nonempty directed walk inside `X`.
- "Order at least `(3/5) |V(D)|`" is stated without division: `3 |V(D)| ≤ 5 |X|`.
-/

namespace OMA.S_opg_large_acyclic_induced_subdigraph_in_a_planar_oriented_graph

/-- An oriented graph: no two opposite arcs (so also no loops). -/
def IsOriented {V : Type} (G : Digraph V) : Prop :=
  ∀ u v, G.Adj u v → ¬ G.Adj v u

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

/-- The subdigraph of `G` induced by `X` has no directed cycle. -/
def IsAcyclicOn {V : Type} (G : Digraph V) (X : Set V) : Prop :=
  ∀ v ∈ X, ¬ Relation.TransGen (fun a b => a ∈ X ∧ b ∈ X ∧ G.Adj a b) v v

theorem main :
    ∀ (V : Type) [Fintype V] (D : Digraph V),
      IsOriented D → IsPlanar (SimpleGraph.fromRel D.Adj) →
        ∃ X : Finset V, 3 * Fintype.card V ≤ 5 * X.card ∧ IsAcyclicOn D (X : Set V) := by
  sorry

end OMA.S_opg_large_acyclic_induced_subdigraph_in_a_planar_oriented_graph
