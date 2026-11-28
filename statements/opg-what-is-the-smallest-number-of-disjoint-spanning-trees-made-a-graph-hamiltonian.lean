import Mathlib

/-!
# SpanningPacking
The four questions concern successive minimum-weight spanning trees or one-trees
on a complete simple undirected weighted graph. A one-tree consists of a tree on
the vertices other than a fixed root and two distinct edges incident to the root.
The bound is asked uniformly over finite complete weighted graphs and permissible
choices among the minimum-weight trees.
-/

namespace OMA.S_opg_what_is_the_smallest_number_of_disjoint_spanning_trees_made_a_graph_hamiltonian

open SimpleGraph Finset
open scoped BigOperators

noncomputable def treeCost {V : Type} [Fintype V] (weight : Sym2 V → ℝ)
    (G : SimpleGraph V) : ℝ := by
  classical
  exact ∑ e ∈ G.edgeFinset, weight e

def successiveMinimum {V : Type} [Fintype V] {k : ℕ} (weight : Sym2 V → ℝ)
    (eligible : SimpleGraph V → Prop) (trees : Fin k → SimpleGraph V) : Prop :=
  ∀ i, eligible (trees i) ∧
    (∀ j, j < i → Disjoint (trees i) (trees j)) ∧
    ∀ G : SimpleGraph V, eligible G → (∀ j, j < i → Disjoint G (trees j)) →
      treeCost weight (trees i) ≤ treeCost weight G

def isOneTree {V : Type} [Fintype V] (root : V) (G : SimpleGraph V) : Prop := by
  classical
  exact (G.induce {root}ᶜ).IsTree ∧ G.degree root = 2

def walkSpanningPath {V : Type} {G : SimpleGraph V} {a b : V} (p : G.Walk a b) : Prop :=
  p.IsPath ∧ ∀ v : V, v ∈ p.support

def walkSpanningCycle {V : Type} {G : SimpleGraph V} {a : V} (p : G.Walk a a) : Prop :=
  p.IsCycle ∧ walkSpanningPath p.tail

def hasHamiltonianPath {V : Type} (G : SimpleGraph V) : Prop :=
  ∃ a b : V, ∃ p : G.Walk a b, walkSpanningPath p

def hasHamiltonianCycle {V : Type} (G : SimpleGraph V) : Prop :=
  ∃ a : V, ∃ p : G.Walk a a, walkSpanningCycle p

def containsShortestHamiltonianPath {V : Type} (weight : Sym2 V → ℝ)
    (G : SimpleGraph V) : Prop := by
  classical
  exact ∃ a b : V, ∃ p : G.Walk a b, walkSpanningPath p ∧
    ∀ c d : V, ∀ q : (⊤ : SimpleGraph V).Walk c d, walkSpanningPath q →
      (p.edges.map weight).sum ≤ (q.edges.map weight).sum

def containsShortestHamiltonianCycle {V : Type} (weight : Sym2 V → ℝ)
    (G : SimpleGraph V) : Prop := by
  classical
  exact ∃ a : V, ∃ p : G.Walk a a, walkSpanningCycle p ∧
    ∀ b : V, ∀ q : (⊤ : SimpleGraph V).Walk b b, walkSpanningCycle q →
      (p.edges.map weight).sum ≤ (q.edges.map weight).sum

def noUniformSpanningTreePackingBound : Prop :=
  ∀ k : ℕ, 0 < k → ∃ (V : Type) (finiteVertices : Fintype V),
    let _ := finiteVertices
    ∃ (weight : Sym2 V → ℝ) (trees : Fin k → SimpleGraph V),
      successiveMinimum weight SimpleGraph.IsTree trees ∧
      ¬ hasHamiltonianPath (⨆ i, trees i) ∧
      ¬ containsShortestHamiltonianPath weight (⨆ i, trees i)

def noUniformOneTreePackingBound : Prop :=
  ∀ k : ℕ, 0 < k → ∃ (V : Type) (finiteVertices : Fintype V),
    let _ := finiteVertices
    ∃ (root : V) (weight : Sym2 V → ℝ) (trees : Fin k → SimpleGraph V),
      successiveMinimum weight (isOneTree root) trees ∧
      ¬ hasHamiltonianCycle (⨆ i, trees i) ∧
      ¬ containsShortestHamiltonianCycle weight (⨆ i, trees i)

theorem main : noUniformSpanningTreePackingBound ∧ noUniformOneTreePackingBound := by
  sorry

end OMA.S_opg_what_is_the_smallest_number_of_disjoint_spanning_trees_made_a_graph_hamiltonian
