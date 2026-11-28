import Mathlib

/-!
# Decomposing a connected graph into paths

Source: https://www.openproblemgarden.org/op/decomposing_a_connected_graph_into_paths
Credit: @lzvxck

Gallai's conjecture, as stated in the source: every simple connected graph on `n` vertices can
be decomposed into at most `(n + 1) / 2` paths.

A decomposition into paths is a family of paths of `G` such that every edge of `G` lies on
exactly one of them. "At most `(n + 1) / 2`" (a real bound) is written `2 * m ≤ n + 1` for the
number `m` of paths. Graphs are finite.
-/

namespace OMA.S_opg_decomposing_a_connected_graph_into_paths

/-- `G` decomposes into `m` paths: there are `m` paths of `G` such that every edge of `G`
lies on exactly one of them. -/
def HasPathDecomposition {V : Type*} (G : SimpleGraph V) (m : ℕ) : Prop :=
  ∃ P : Fin m → Σ u v : V, G.Walk u v,
    (∀ i, (P i).2.2.IsPath) ∧
    ∀ e ∈ G.edgeSet, ∃! i, e ∈ (P i).2.2.edges

/-- **Gallai's path decomposition conjecture.** Every connected simple graph on `n` vertices
can be decomposed into at most `(n + 1) / 2` paths. -/
theorem main : ∀ (V : Type) [Fintype V] (G : SimpleGraph V), G.Connected →
    ∃ m : ℕ, 2 * m ≤ Fintype.card V + 1 ∧ HasPathDecomposition G m := by
  sorry

end OMA.S_opg_decomposing_a_connected_graph_into_paths
