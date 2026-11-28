import Mathlib

/-!
# Acyclic edge-colouring

Source: http://www.openproblemgarden.org/op/acyclic_edge_coloring
Credit: @shc261392

Conjecture (Fiamčík; also Alon, Sudakov and Zaks): every simple graph with maximum degree `Δ` has
a proper `(Δ + 2)`-edge-colouring such that every cycle contains edges of at least three distinct
colours.

Reading used here:
* Graphs are finite simple graphs; `Δ` is `G.maxDegree`.
* An edge-colouring is a map `c : Sym2 V → Fin (Δ + 2)`; only its values on edges matter. It is
  proper when two distinct edges `uv`, `uw` sharing the vertex `u` get different colours.
* A cycle is a closed walk with `IsCycle`; its edges are `p.edges`, and the condition is that the
  set of colours on them has at least `3` elements.
-/

namespace OMA.S_opg_acyclic_edge_coloring

theorem main :
    ∀ (V : Type) [Fintype V] (G : SimpleGraph V) [DecidableRel G.Adj],
      ∃ c : Sym2 V → Fin (G.maxDegree + 2),
        (∀ u v w : V, G.Adj u v → G.Adj u w → v ≠ w → c s(u, v) ≠ c s(u, w)) ∧
        ∀ (x : V) (p : G.Walk x x), p.IsCycle → 3 ≤ (p.edges.map c).toFinset.card := by
  sorry

end OMA.S_opg_acyclic_edge_coloring
