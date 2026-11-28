import Mathlib

/-!
# Complete bipartite subgraphs of perfect graphs

Source: https://www.openproblemgarden.org/op/complete_bipartite_subgraphs_of_perfect_graphs
Credit: @lzvxck

The source: let `G` be a perfect graph on `n` vertices. Is it true that either `G` or `Ḡ`
contains a complete bipartite subgraph with bipartition `(A, B)` so that
`|A|, |B| ≥ n^{1 - o(1)}`?

The affirmative form is stated. Conventions: graphs are finite and simple. `G` is perfect when
every induced subgraph `G[S]` has chromatic number equal to its clique number. A complete
bipartite subgraph with bipartition `(A, B)` is a pair of disjoint vertex sets with every
vertex of `A` adjacent to every vertex of `B` (not necessarily induced). The bound
`n^{1 - o(1)}` is read in the usual way: for every `ε > 0` there is `N` such that the bound
`n^{1 - ε}` holds for all `n ≥ N`.
-/

namespace OMA.S_opg_complete_bipartite_subgraphs_of_perfect_graphs

/-- `G` is perfect: every induced subgraph has chromatic number equal to its clique number. -/
def IsPerfect {V : Type*} (G : SimpleGraph V) : Prop :=
  ∀ S : Set V, (G.induce S).chromaticNumber = ((G.induce S).cliqueNum : ℕ∞)

/-- `G` contains a complete bipartite subgraph with parts of size at least `a`. -/
def HasBiclique {V : Type*} (G : SimpleGraph V) (a : ℝ) : Prop :=
  ∃ A B : Finset V, Disjoint A B ∧ a ≤ A.card ∧ a ≤ B.card ∧ ∀ x ∈ A, ∀ y ∈ B, G.Adj x y

/-- **Complete bipartite subgraphs of perfect graphs (Fox).** For every `ε > 0` and all large
`n`, every perfect graph `G` on `n` vertices has, in `G` or in its complement, a complete
bipartite subgraph with both parts of size at least `n^{1 - ε}`. -/
theorem main : ∀ ε : ℝ, 0 < ε → ∃ N : ℕ, ∀ (V : Type) [Fintype V] (G : SimpleGraph V),
    N ≤ Fintype.card V → IsPerfect G →
      HasBiclique G ((Fintype.card V : ℝ) ^ (1 - ε)) ∨
        HasBiclique Gᶜ ((Fintype.card V : ℝ) ^ (1 - ε)) := by
  sorry

end OMA.S_opg_complete_bipartite_subgraphs_of_perfect_graphs
