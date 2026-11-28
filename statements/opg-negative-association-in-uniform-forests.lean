import Mathlib

/-!
# Negative association in uniform forests

Source: https://www.openproblemgarden.org/op/negative_association_in_uniform_forests
Credit: @ishaanzee

**Conjecture** (R. Pemantle). Let `G` be a finite graph, let `e, f ∈ E(G)`, and let `F` be the edge
set of a forest chosen uniformly at random from all forests of `G`. Then
`P(e ∈ F | f ∈ F) ≤ P(e ∈ F)`.

Formalization:
* `G` is a finite simple graph; `e ≠ f` are two edges (for `e = f` the left side is `1`).
* The forests of `G` are the edge sets `F ⊆ E(G)` such that the graph with edge set `F` is acyclic.
* With `N` the number of forests, `N_e`, `N_f` the numbers containing `e`, resp. `f`, and `N_{ef}`
  the number containing both, the inequality `N_{ef} / N_f ≤ N_e / N` is `N_{ef} · N ≤ N_e · N_f`
  (all counts are positive since the empty forest and the single edges are forests).
-/

namespace OMA.S_opg_negative_association_in_uniform_forests

/-- The number of forests of `G` (acyclic edge subsets) containing all edges in `S`. -/
noncomputable def numForests {V : Type*} (G : SimpleGraph V) (S : Set (Sym2 V)) : ℕ :=
  {F : Set (Sym2 V) | F ⊆ G.edgeSet ∧ (SimpleGraph.fromEdgeSet F).IsAcyclic ∧ S ⊆ F}.ncard

/-- **Pemantle's conjecture**: in a uniformly random forest, the events `e ∈ F` and `f ∈ F` are
negatively correlated. -/
theorem main : ∀ (V : Type) [Fintype V] (G : SimpleGraph V) (e f : Sym2 V),
    e ∈ G.edgeSet → f ∈ G.edgeSet → e ≠ f →
      numForests G {e, f} * numForests G ∅ ≤ numForests G {e} * numForests G {f} := by
  sorry

end OMA.S_opg_negative_association_in_uniform_forests
