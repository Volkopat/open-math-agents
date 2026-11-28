import Mathlib

/-!
# 3-Decomposition Conjecture

Source: http://www.openproblemgarden.org/op/3_decomposition_conjecture
Credit: @shc261392

Conjecture (Hoffmann-Ostenhof): every connected cubic graph has a decomposition into a spanning
tree, a family of cycles and a matching. In the precise form of the source: a connected cubic
graph `G` contains a spanning tree `T`, a `2`-regular subgraph `C` and a matching `M` (where only
`T` is required to be nonempty; `C` or `M` may be empty) whose edge sets cover `E(G)` and are
pairwise disjoint.

Reading used here:
* `G` is a finite simple graph, connected, with every degree equal to `3`.
* `T`, `C`, `M` are subgraphs given as `SimpleGraph V` on the whole vertex type, compared by
  edges: `T ⊔ C ⊔ M = G` and pairwise `Disjoint` (no common edge).
* `T.IsTree` makes `T` a spanning tree (connected and acyclic on all of `V`).
* "`C` is `2`-regular" for a possibly empty subgraph: every vertex has degree `0` or `2` in `C`
  (the vertices of degree `2` are the vertices of the cycles).
* "`M` is a matching": every vertex has degree at most `1` in `M`.
* Degrees are counted as `Set.ncard` of neighbour sets.
-/

namespace OMA.S_opg_3_decomposition_conjecture

theorem main :
    ∀ (V : Type) [Fintype V] (G : SimpleGraph V), G.Connected →
      (∀ v : V, (G.neighborSet v).ncard = 3) →
        ∃ T C M : SimpleGraph V, T ⊔ C ⊔ M = G ∧
          Disjoint T C ∧ Disjoint T M ∧ Disjoint C M ∧
          T.IsTree ∧
          (∀ v : V, (C.neighborSet v).ncard = 0 ∨ (C.neighborSet v).ncard = 2) ∧
          (∀ v : V, (M.neighborSet v).ncard ≤ 1) := by
  sorry

end OMA.S_opg_3_decomposition_conjecture
