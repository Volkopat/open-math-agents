import Mathlib

/-!
# The Two Color Conjecture

Source: https://www.openproblemgarden.org/op/partitioning_planar_digraphs
Credit: @pyaf

Conjecture (Neumann-Lara): if `G` is an orientation of a simple planar graph, then there is a
partition of `V(G)` into `{X₁, X₂}` so that the graph induced by `Xᵢ` is acyclic for `i = 1, 2`.

Conventions:
- An orientation of a simple graph is an oriented graph: a finite Mathlib `Digraph V` with no
  pair of opposite arcs, hence no loops (`IsOriented`, reused verbatim from
  `statements/opg-seymours-second-neighbourhood-conjecture.lean`). The simple graph it orients
  is its underlying graph `SimpleGraph.fromRel D.Adj`, in which `u ~ v` iff `u ≠ v` and
  `u → v` or `v → u`.
- A graph is planar if it has a plane drawing: distinct points of `ℝ²` for the vertices and,
  for every edge, an arc (a continuous injective image of `[0, 1]`) joining its endpoints,
  whose interior meets no vertex and no other edge's interior (`IsPlanar`, reused verbatim from
  `statements/wp-apex-graph.lean`).
- The subdigraph induced by `X` is acyclic if it has no directed cycle: no vertex of `X` reaches
  itself by a nonempty directed walk inside `X`.
- The partition is given by a map `c : V → Fin 2` with `Xᵢ = c⁻¹(i)`; as usual for colourings
  a part may be empty (equivalently, the dichromatic number is at most `2`).
-/

namespace OMA.S_opg_partitioning_planar_digraphs

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
    ∀ (V : Type) [Fintype V] (G : Digraph V),
      IsOriented G → IsPlanar (SimpleGraph.fromRel G.Adj) →
        ∃ c : V → Fin 2, ∀ i, IsAcyclicOn G {v | c v = i} := by
  sorry

end OMA.S_opg_partitioning_planar_digraphs
