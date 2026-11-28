import Mathlib

/-!
# Highly connected graphs with no K_n minor

Source: https://www.openproblemgarden.org/op/high_connectivity_no_k_n
Credit: @pyaf

Problem (Thomas): Is it true for all `n ≥ 0` that every sufficiently large `n`-connected graph
without a `K_n` minor has a set of `n - 5` vertices whose deletion results in a planar graph?

`main` asserts the affirmative answer; a disproof refutes it. Norin and Thomas have announced
a proof (talk slides; no published paper found).

Conventions (standard, as in Diestel's *Graph Theory*, and copied from the merged statement
`wp-apex-graph` of Jørgensen's conjecture):
- Graphs are finite simple graphs, given as a `SimpleGraph` on a finite vertex type `V`.
- `G` is `k`-connected if it has more than `k` vertices and `G - X` is connected for every set
  `X` of fewer than `k` vertices.
- `H` is a minor of `G` if there are pairwise disjoint, nonempty vertex sets `B w ⊆ V(G)`
  (one per vertex `w` of `H`), each inducing a connected subgraph of `G`, such that whenever
  `w w'` is an edge of `H` some vertex of `B w` is adjacent in `G` to some vertex of `B w'`.
- A graph is planar if it has a plane drawing: distinct points of `ℝ²` for the vertices and,
  for every edge, an arc (a continuous injective image of `[0, 1]`) joining its endpoints,
  whose interior meets no vertex and no other edge's interior.
- "Sufficiently large": for each `n` there is `N` such that the claim holds for every graph
  with at least `N` vertices.
- `n - 5` is truncated subtraction in `ℕ`, so for `n ≤ 5` the claim is that the graph itself
  is planar; this matches the source, which calls the cases `n ≤ 4` trivial (no `K_4` minor
  implies planar) and derives `n = 5` from Wagner's theorem. Since deleting further vertices
  preserves planarity, "a set of `n - 5` vertices" and "at most `n - 5` vertices" agree on
  graphs with at least `n - 5` vertices.
-/

namespace OMA.S_opg_high_connectivity_no_k_n

open SimpleGraph

/-- `G` is `k`-vertex-connected: more than `k` vertices, and deleting fewer than `k` vertices
leaves a connected graph. -/
def IsKVertexConnected {V : Type} [Fintype V] (G : SimpleGraph V) (k : ℕ) : Prop :=
  k < Fintype.card V ∧
    ∀ X : Finset V, X.card < k → (G.induce ((X : Set V)ᶜ)).Connected

/-- `H` is a minor of `G`, witnessed by branch sets `B w`. -/
def IsMinor {W V : Type} (H : SimpleGraph W) (G : SimpleGraph V) : Prop :=
  ∃ B : W → Set V,
    (∀ w, (B w).Nonempty) ∧
    (∀ w w', w ≠ w' → Disjoint (B w) (B w')) ∧
    (∀ w, (G.induce (B w)).Connected) ∧
    (∀ w w', H.Adj w w' → ∃ x ∈ B w, ∃ y ∈ B w', G.Adj x y)

/-- `G` has a plane drawing: vertices at distinct points, edges as arcs joining their endpoints,
with arc interiors avoiding all vertices and the interiors of all other arcs. -/
def IsPlanar {V : Type} (G : SimpleGraph V) : Prop :=
  ∃ (pos : V → ℝ × ℝ) (arc : G.edgeSet → C(unitInterval, ℝ × ℝ)),
    Function.Injective pos ∧
    (∀ e, Function.Injective (arc e)) ∧
    (∀ e, Sym2.map pos e.1 = s(arc e 0, arc e 1)) ∧
    (∀ e (t : unitInterval), (t : ℝ) ∈ Set.Ioo 0 1 → ∀ v, arc e t ≠ pos v) ∧
    (∀ e f, e ≠ f → ∀ s t : unitInterval, (s : ℝ) ∈ Set.Ioo 0 1 → (t : ℝ) ∈ Set.Ioo 0 1 →
      arc e s ≠ arc f t)

theorem main :
    ∀ n : ℕ, ∃ N : ℕ, ∀ (V : Type) [Fintype V] (G : SimpleGraph V), N ≤ Fintype.card V →
      IsKVertexConnected G n → ¬ IsMinor (⊤ : SimpleGraph (Fin n)) G →
        ∃ X : Finset V, X.card = n - 5 ∧ IsPlanar (G.induce ((X : Set V)ᶜ)) := by
  sorry

end OMA.S_opg_high_connectivity_no_k_n
