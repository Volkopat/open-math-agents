import Mathlib

/-!
# Lovász–Woodall conjecture

Source: https://en.wikipedia.org/wiki/Lov%C3%A1sz%E2%80%93Woodall_conjecture
Credit: @mgv27

If L is a set of k independent edges in a k-connected graph G, and either k is even or G − L is
connected, then G has a cycle containing every edge of L. Known for small k; Kawarabayashi
proved an approximate version.

Formalization notes:
* `G` is a finite simple graph. `k`-connected: more than `k` vertices, and deleting any set of
  fewer than `k` vertices leaves a connected induced subgraph.
* `L` is a finset of `k` edges of `G`, pairwise vertex-disjoint (a matching).
* We take `k ≥ 2`; for `k = 0` the statement would require every graph to have a cycle.
* A cycle is a closed walk `p` with `p.IsCycle`; it contains `e` when `e ∈ p.edges`.
-/

namespace OMA.S_wpc_lovasz_woodall_conjecture

open SimpleGraph

/-- `G` is `k`-vertex-connected: it has more than `k` vertices and removing any fewer than `k`
vertices leaves it connected. -/
def IsKConnected {V : Type*} [Fintype V] (G : SimpleGraph V) (k : ℕ) : Prop :=
  k < Fintype.card V ∧
    ∀ S : Finset V, S.card < k → (G.induce ((S : Set V)ᶜ)).Connected

/-- `L` is a set of independent (pairwise vertex-disjoint) edges of `G`. -/
def IsIndependentEdges {V : Type*} (G : SimpleGraph V) (L : Finset (Sym2 V)) : Prop :=
  (L : Set (Sym2 V)) ⊆ G.edgeSet ∧
    ∀ e ∈ L, ∀ f ∈ L, e ≠ f → ∀ v : V, v ∈ e → v ∉ f

/-- Lovász–Woodall conjecture. -/
theorem main : ∀ (V : Type) [Fintype V] [DecidableEq V] (G : SimpleGraph V) (k : ℕ),
    2 ≤ k → IsKConnected G k → ∀ L : Finset (Sym2 V), IsIndependentEdges G L → L.card = k →
    (Even k ∨ (G.deleteEdges (L : Set (Sym2 V))).Connected) →
    ∃ (v : V) (p : G.Walk v v), p.IsCycle ∧ ∀ e ∈ L, e ∈ p.edges := by
  sorry

end OMA.S_wpc_lovasz_woodall_conjecture
