import Mathlib

/-!
# Decomposing an eulerian graph into cycles

Source: https://www.openproblemgarden.org/op/decomposing_an_eulerian_graph_into_cycles
Credit: @ishaanzee

**Conjecture** (G. Hajós). Every simple eulerian graph on `n` vertices can be decomposed into at
most `(n - 1) / 2` cycles.

The bound is tight: a complete graph on `2k + 1` vertices cannot be covered by fewer than `k`
cycles.

Formalization:
* An eulerian graph is a finite simple graph that is connected and has all degrees even. (Since
  the bound is additive over components, this is equivalent to the version for all graphs with
  even degrees.)
* A cycle is the edge set of a closed walk that is a cycle (`SimpleGraph.Walk.IsCycle`). A
  decomposition into cycles is a finite family of cycles whose edge sets are pairwise disjoint
  and cover every edge.
* "At most `(n - 1)/2` cycles" is `2 * (number of cycles) ≤ n - 1`.
-/

namespace OMA.S_opg_decomposing_an_eulerian_graph_into_cycles

/-- `S` is the edge set of some cycle of `G`. -/
def IsCycleEdgeSet {V : Type*} [DecidableEq V] (G : SimpleGraph V) (S : Finset (Sym2 V)) : Prop :=
  ∃ (v : V) (c : G.Walk v v), c.IsCycle ∧ c.edges.toFinset = S

/-- **Hajós' conjecture** on cycle decompositions: every connected finite simple graph with all
degrees even, on `n` vertices, has its edge set partitioned into at most `(n - 1)/2` cycles. -/
theorem main : ∀ (V : Type) [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj],
    G.Connected → (∀ v, Even (G.degree v)) →
      ∃ D : Finset (Finset (Sym2 V)), (∀ S ∈ D, IsCycleEdgeSet G S) ∧
        (D : Set (Finset (Sym2 V))).PairwiseDisjoint id ∧ D.sup id = G.edgeFinset ∧
        2 * D.card ≤ Fintype.card V - 1 := by
  sorry

end OMA.S_opg_decomposing_an_eulerian_graph_into_cycles
