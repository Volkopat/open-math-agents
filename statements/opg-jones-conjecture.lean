import Mathlib

/-!
# Jones' conjecture

Source: https://www.openproblemgarden.org/op/jones_conjecture
Credit: @pyaf

For a graph `G`, let `cp(G)` be the cardinality of a maximum cycle packing (a collection of
vertex-disjoint cycles) and `cc(G)` the cardinality of a minimum feedback vertex set (a set of
vertices `X` such that `G - X` is acyclic).

Conjecture (Kloks, Lee, Liu): for every planar graph `G`, `cc(G) ≤ 2 cp(G)`.

Conventions (standard, as in the source's reference [KLL]):
- Graphs are finite simple graphs, given as a `SimpleGraph` on a finite vertex type `V`.
- A cycle is a closed walk with `SimpleGraph.Walk.IsCycle` (at least three vertices, no repeated
  vertex or edge). Cycles of a packing are vertex-disjoint: their supports share no vertex.
- `G - X` is the subgraph induced on the complement of `X`; it is acyclic if it is a forest
  (`SimpleGraph.IsAcyclic`).
- A graph is planar if it has a plane drawing: distinct points of `ℝ²` for the vertices and,
  for every edge, an arc (a continuous injective image of `[0, 1]`) joining its endpoints,
  whose interior meets no vertex and no other edge's interior (definition reused verbatim from
  `statements/wp-apex-graph.lean`).
-/

namespace OMA.S_opg_jones_conjecture

open SimpleGraph

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

/-- `G` contains `k` pairwise vertex-disjoint cycles. -/
def HasCyclePacking {V : Type} (G : SimpleGraph V) (k : ℕ) : Prop :=
  ∃ c : Fin k → Σ v : V, G.Walk v v,
    (∀ i, (c i).2.IsCycle) ∧
    ∀ i j, i ≠ j → ∀ v, v ∈ (c i).2.support → v ∉ (c j).2.support

/-- `cp(G)`: the maximum number of vertex-disjoint cycles in `G`. -/
noncomputable def cyclePackingNumber {V : Type} (G : SimpleGraph V) : ℕ :=
  sSup {k | HasCyclePacking G k}

/-- `cc(G)`: the minimum size of a feedback vertex set, a set `X` with `G - X` acyclic. -/
noncomputable def feedbackVertexNumber {V : Type} (G : SimpleGraph V) : ℕ :=
  sInf {k | ∃ X : Finset V, X.card = k ∧ (G.induce ((X : Set V)ᶜ)).IsAcyclic}

theorem main :
    ∀ (V : Type) [Fintype V] (G : SimpleGraph V),
      IsPlanar G → feedbackVertexNumber G ≤ 2 * cyclePackingNumber G := by
  sorry

end OMA.S_opg_jones_conjecture
