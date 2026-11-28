import Mathlib

/-!
# Uniquely restricted matchings in subcubic graphs and bridges

Source: https://arxiv.org/abs/1805.00840, Conjecture 2
(Maximilian Fürst, Michael A. Henning and Dieter Rautenbach)
Credit: @pyaf

A matching M of G is uniquely restricted if no other matching of G covers the
same set of vertices. Conjecture: every connected subcubic graph G with m
edges and b bridges, other than K₃,₃, has a uniquely restricted matching of
size at least (m + b)/6. The paper proves it with b replaced by the number of
bridges on a path between two vertices of degree at most 2. Searches of arXiv
for later work on uniquely restricted matchings (arXiv:1810.04473,
1807.08981, 2508.12004) found no resolution.

A matching is a subgraph in which every vertex has exactly one neighbour,
so its vertex set is exactly the set of covered vertices.
-/

namespace OMA.S_arxiv_1805_00840

open SimpleGraph

/-- No other matching of G covers the same vertices as M. -/
def IsUniquelyRestricted {V : Type*} {G : SimpleGraph V} (M : G.Subgraph) : Prop :=
  M.IsMatching ∧ ∀ M' : G.Subgraph, M'.IsMatching → M'.verts = M.verts → M' = M

theorem main : ∀ (V : Type) [Fintype V] (G : SimpleGraph V) [DecidableRel G.Adj],
    G.Connected → (∀ v, G.degree v ≤ 3) →
    IsEmpty (G ≃g completeBipartiteGraph (Fin 3) (Fin 3)) →
    ∃ M : G.Subgraph, IsUniquelyRestricted M ∧
      G.edgeFinset.card + {e ∈ G.edgeSet | G.IsBridge e}.ncard ≤ 6 * M.edgeSet.ncard := by
  sorry

end OMA.S_arxiv_1805_00840
