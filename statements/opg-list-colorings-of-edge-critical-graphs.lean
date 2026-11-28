import Mathlib

/-!
# List colorings of edge-critical graphs

Source: https://www.openproblemgarden.org/op/list_colorings_of_edge_critical_graphs
Credit: @ishaanzee

**Conjecture** (B. Mohar). Suppose that `G` is a `Δ`-edge-critical graph. Suppose that for each edge
`e` of `G`, there is a list `L(e)` of `Δ` colors. Then `G` is `L`-edge-colorable unless all lists
are equal to each other.

A graph `G` is `Δ`-edge-critical if it is not `Δ`-edge-colorable but every edge-deleted subgraph is
`Δ`-edge-colorable (here `Δ` is the maximum degree of `G`).

Formalization:
* Graphs are finite simple graphs; `Δ` is Mathlib's `maxDegree`.
* An edge coloring is a map on `Sym2 V` (only values on edges matter); it is proper when two
  distinct edges sharing a vertex get different colors. `Δ`-edge-colorable: a proper edge coloring
  with values in `Fin Δ`. `G - e` is `G.deleteEdges {e}`.
* Lists are `L : Sym2 V → Finset ℕ` with `|L(e)| = Δ` for every edge `e`; `G` is `L`-edge-colorable
  if some proper edge coloring `c : Sym2 V → ℕ` has `c e ∈ L e` for every edge `e`.
-/

namespace OMA.S_opg_list_colorings_of_edge_critical_graphs

/-- `c` is a proper edge coloring of `G`: distinct edges sharing a vertex get different colors. -/
def IsProperEdgeColoring {V : Type*} {α : Type*} (G : SimpleGraph V) (c : Sym2 V → α) : Prop :=
  ∀ u v w : V, G.Adj u v → G.Adj u w → v ≠ w → c s(u, v) ≠ c s(u, w)

/-- `G` is `k`-edge-colorable. -/
def EdgeColorable {V : Type*} (G : SimpleGraph V) (k : ℕ) : Prop :=
  ∃ c : Sym2 V → Fin k, IsProperEdgeColoring G c

/-- **Mohar's conjecture.** -/
theorem main : ∀ (V : Type) [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj],
    ¬ EdgeColorable G G.maxDegree →
    (∀ e ∈ G.edgeSet, EdgeColorable (G.deleteEdges {e}) G.maxDegree) →
    ∀ L : Sym2 V → Finset ℕ, (∀ e ∈ G.edgeSet, (L e).card = G.maxDegree) →
      (∃ c : Sym2 V → ℕ, IsProperEdgeColoring G c ∧ ∀ e ∈ G.edgeSet, c e ∈ L e) ∨
        ∀ e ∈ G.edgeSet, ∀ e' ∈ G.edgeSet, L e = L e' := by
  sorry

end OMA.S_opg_list_colorings_of_edge_critical_graphs
