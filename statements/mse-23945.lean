import Mathlib

/-!
# Reconstruction Conjecture for Partial 2-Trees (Series-Parallel Graphs)

Source: https://math.stackexchange.com/questions/23945/reconstruction-conjecture-and-partial-2-trees
-- Credit: @Dugongue (agent: Claude Code, model claude-opus-5-5)
-- Draft from an earlier generic agent run; audited against the source and checked by this agent.

## Problem Statement
The Reconstruction Conjecture states that every finite simple graph with at least
3 vertices is uniquely determined up to isomorphism by its multiset (deck) of
vertex-deleted subgraphs.
Are all partial 2-trees (equivalently, finite simple graphs with no `K₄` minor,
i.e. graphs of treewidth at most 2) reconstructible?

## Formalization Notes
A finite simple graph `G` on `V` is a partial 2-tree iff it has no `K₄` minor.
We define `HasK4Minor G` via four pairwise disjoint nonempty subsets `B₀, B₁, B₂, B₃`
of vertices, each inducing a connected subgraph of `G`, with at least one edge
between `Bᵢ` and `Bⱼ` for all `i ≠ j`.
Two graphs `G, H` on `V` have the same deck iff there is a bijection `σ : V ≃ V`
such that for every `v : V`, the induced subgraph of `G` on `{u | u ≠ v}` is
isomorphic to the induced subgraph of `H` on `{u | u ≠ σ v}`.
-/

namespace OMA.S_mse_23945

def HasK4Minor {V : Type} (G : SimpleGraph V) : Prop :=
  ∃ B : Fin 4 → Set V,
    (∀ i, (B i).Nonempty) ∧
    (∀ i j, i ≠ j → Disjoint (B i) (B j)) ∧
    (∀ i, (G.induce (B i)).Connected) ∧
    (∀ i j, i ≠ j → ∃ u ∈ B i, ∃ v ∈ B j, G.Adj u v)

def SameDeck {V : Type} (G H : SimpleGraph V) : Prop :=
  ∃ σ : V ≃ V, ∀ v : V,
    Nonempty ((G.induce {u : V | u ≠ v}) ≃g (H.induce {u : V | u ≠ σ v}))

theorem main :
    ∀ (V : Type) [Fintype V], 3 ≤ Fintype.card V →
      ∀ G H : SimpleGraph V,
        ¬ HasK4Minor G → ¬ HasK4Minor H → SameDeck G H →
        Nonempty (G ≃g H) := by
  sorry

end OMA.S_mse_23945
