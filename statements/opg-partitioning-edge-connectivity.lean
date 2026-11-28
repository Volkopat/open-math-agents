import Mathlib

/-!
# Partitioning edge-connectivity

Source: https://www.openproblemgarden.org/op/partitioning_edge_connectivity
Credit: @shc261392

Question (DeVos): let `G` be an `(a+b+2)`-edge-connected graph. Does there exist a partition
`{A, B}` of `E(G)` so that `(V, A)` is `a`-edge-connected and `(V, B)` is `b`-edge-connected?
Stated here in the affirmative.

Reading used here:
* Graphs may have parallel edges (the source works with edge-cuts, and the Nash-Williams/Tutte
  argument it cites is for multigraphs). A finite multigraph is a finite vertex type `V`, a
  finite edge type `E` and a map `ends : E → Sym2 V`; loops are excluded.
* An edge set `A` is `k`-edge-connected on `V` when, after deleting any set of fewer than `k`
  edges, the edges left in `A` still join every pair of vertices by a path. With `k = 0` this
  condition is empty.
* The partition is `A` together with its complement `Aᶜ`.
-/

namespace OMA.S_opg_partitioning_edge_connectivity

/-- The spanning subgraph with edge set `A` is `k`-edge-connected. -/
def EdgeConn {V E : Type} (k : ℕ) (ends : E → Sym2 V) (A : Set E) : Prop :=
  ∀ F : Finset E, F.card < k →
    ∀ x y : V, Relation.ReflTransGen (fun u v => ∃ e ∈ A, e ∉ F ∧ ends e = s(u, v)) x y

theorem main :
    ∀ (a b : ℕ) (V E : Type) [Fintype V] [Fintype E] (ends : E → Sym2 V),
      (∀ e, ¬ (ends e).IsDiag) → EdgeConn (a + b + 2) ends Set.univ →
        ∃ A : Set E, EdgeConn a ends A ∧ EdgeConn b ends Aᶜ := by
  sorry

end OMA.S_opg_partitioning_edge_connectivity
