import Mathlib

/-!
# Graham's conjecture on tree reconstruction

Source: https://www.openproblemgarden.org/op/grahams_conjecture_on_tree_reconstruction
Credit: @ishaanzee

**Problem** (R. L. Graham). For every graph `G`, let `L(G)` denote the line graph of `G`. Given
that `G` is a tree, can we determine it from the integer sequence
`|V(G)|, |V(L(G))|, |V(L(L(G)))|, …`?

We state the affirmative answer: two finite trees with the same sequence are isomorphic.

Formalization:
* A graph is bundled with its vertex type (`Σ V : Type, SimpleGraph V`) so that the line graph
  can be iterated: `lineStep ⟨V, G⟩ = ⟨E(G), L(G)⟩`, with Mathlib's `SimpleGraph.lineGraph`, whose
  vertex type is the edge set of `G`.
* The `k`-th term of the sequence is the number of vertices of `L^k(G)` (`Nat.card`; all these
  graphs are finite).
-/

namespace OMA.S_opg_grahams_conjecture_on_tree_reconstruction

/-- One application of the line graph operator to a graph bundled with its vertex type. -/
def lineStep (X : Σ V : Type, SimpleGraph V) : Σ V : Type, SimpleGraph V :=
  ⟨X.2.edgeSet, X.2.lineGraph⟩

/-- `lineSeq X k = |V(L^k(X))|`. -/
noncomputable def lineSeq (X : Σ V : Type, SimpleGraph V) (k : ℕ) : ℕ :=
  Nat.card (lineStep^[k] X).1

/-- **Graham's tree reconstruction conjecture**: finite trees with the same sequence of iterated
line graph orders are isomorphic. -/
theorem main : ∀ (V W : Type) [Finite V] [Finite W] (T : SimpleGraph V) (T' : SimpleGraph W),
    T.IsTree → T'.IsTree → (∀ k : ℕ, lineSeq ⟨V, T⟩ k = lineSeq ⟨W, T'⟩ k) →
      Nonempty (T ≃g T') := by
  sorry

end OMA.S_opg_grahams_conjecture_on_tree_reconstruction
