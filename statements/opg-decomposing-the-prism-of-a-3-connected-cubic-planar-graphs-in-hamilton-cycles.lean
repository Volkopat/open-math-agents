import Mathlib

/-!
# Hamilton decomposition of prisms over 3-connected cubic planar graphs

Source: https://www.openproblemgarden.org/op/decomposing_the_prism_of_a_3_connected_cubic_planar_graphs_in_hamilton_cycles

Conjecture (Alspach, Rosenfeld): every prism over a `3`-connected cubic planar graph can be
decomposed into two Hamilton cycles. The prism over `G` is the Cartesian product `G □ K₂`.

Conventions:
- Graphs are finite simple graphs, given as a `SimpleGraph` on a finite vertex type `V`.
- `G` is `k`-connected if it has more than `k` vertices and deleting any set of fewer than `k`
  vertices leaves it connected; cubic means `3`-regular. Both definitions and the
  plane-drawing definition of planarity are copied verbatim from
  `statements/wp-apex-graph.lean`.
- The prism is Mathlib's box product `G □ ⊤` with `⊤` the complete graph on `Fin 2`.
- A decomposition into two Hamilton cycles: two Hamiltonian cycles of the prism such that every
  edge of the prism lies on exactly one of them.
-/

namespace OMA.S_opg_decomposing_the_prism_of_a_3_connected_cubic_planar_graphs_in_hamilton_cycles

open SimpleGraph

/-- `G` is `k`-vertex-connected: more than `k` vertices, and deleting fewer than `k` vertices
leaves a connected graph. -/
def IsKVertexConnected {V : Type} [Fintype V] (G : SimpleGraph V) (k : ℕ) : Prop :=
  k < Fintype.card V ∧
    ∀ X : Finset V, X.card < k → (G.induce ((X : Set V)ᶜ)).Connected

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

/-- `H` decomposes into two Hamilton cycles: two Hamiltonian cycles of `H` such that every edge
of `H` lies on exactly one of them. -/
def HasHamiltonDecomposition {W : Type} [Fintype W] [DecidableEq W] (H : SimpleGraph W) : Prop :=
  ∃ (x y : W) (a : H.Walk x x) (b : H.Walk y y), a.IsHamiltonianCycle ∧ b.IsHamiltonianCycle ∧
    ∀ e ∈ H.edgeSet, (e ∈ a.edges ↔ e ∉ b.edges)

/-- The prism `G □ K₂` over every `3`-connected cubic planar graph `G` decomposes into two
Hamilton cycles. -/
theorem main :
    ∀ (V : Type) [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj],
      IsKVertexConnected G 3 → G.IsRegularOfDegree 3 → IsPlanar G →
        HasHamiltonDecomposition (G □ (⊤ : SimpleGraph (Fin 2))) := by
  sorry

end OMA.S_opg_decomposing_the_prism_of_a_3_connected_cubic_planar_graphs_in_hamilton_cycles
