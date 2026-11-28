import Mathlib

/-!
# (m,n)-cycle covers

Source: https://www.openproblemgarden.org/op/m_n_cycle_covers
Credit: @ishaanzee

**Conjecture** (U. Celmins, M. Preissmann). Every bridgeless graph has a `(5,2)`-cycle-cover.

Definition: if `G = (V, E)` is a graph, a binary cycle of `G` is a set `C ⊆ E` such that every
vertex of the graph `(V, C)` has even degree. An `(m, n)`-cycle-cover of `G` is a list `L`
consisting of `m` cycles so that every edge of `G` is contained in exactly `n` of these cycles.

Formalization:
* Graphs are finite simple graphs (the source allows graphs in general; this statement covers the
  simple ones); bridgeless means no edge is a bridge (`SimpleGraph.IsBridge`).
* A binary cycle is a finite set `C` of edges of `G` in which every vertex has an even number of
  incident edges.
* A `(5,2)`-cycle-cover is a family `C : Fin 5 → Finset (Sym2 V)` of binary cycles such that every
  edge of `G` lies in exactly two of them.
-/

namespace OMA.S_opg_m_n_cycle_covers

/-- `C` is a binary cycle of `G`: a set of edges of `G` with every vertex of even degree. -/
def IsBinaryCycle {V : Type*} [Fintype V] [DecidableEq V] (G : SimpleGraph V)
    (C : Finset (Sym2 V)) : Prop :=
  (∀ e ∈ C, e ∈ G.edgeSet) ∧ ∀ v : V, Even (Finset.univ.filter fun w => s(v, w) ∈ C).card

/-- **Celmins–Preissmann conjecture**: every bridgeless graph has a `(5,2)`-cycle-cover. -/
theorem main : ∀ (V : Type) [Fintype V] [DecidableEq V] (G : SimpleGraph V),
    (∀ e ∈ G.edgeSet, ¬ G.IsBridge e) →
      ∃ C : Fin 5 → Finset (Sym2 V), (∀ i, IsBinaryCycle G (C i)) ∧
        ∀ e ∈ G.edgeSet, (Finset.univ.filter fun i => e ∈ C i).card = 2 := by
  sorry

end OMA.S_opg_m_n_cycle_covers
