import Mathlib

/-!
# Polynomial invariants for rooted trees related to their random destruction

Source: https://arxiv.org/abs/2302.08394 (Fabian Burghart), abstract, Preliminaries, Definition 2
and Remark 16.
Credit: @ivillar

Abstract of the source: We consider three bivariate polynomial invariants $P$, $A$, and $S$ for
rooted trees, as well as a trivariate polynomial invariant $M$. [...] The main result states that
the invariants $P$ and $S$ are complete, that is they distinguish rooted trees (in fact, even
rooted forests) up to isomorphism. [...] For $A$, we provide counterexamples showing that it is
not complete.

Formalization notes:
* Preliminaries of the source: a rooted tree is a finite tree with a distinguished vertex, the
  root; a leaf is a vertex without children; an isomorphism of rooted trees is a graph
  isomorphism that maps the root to the root. Here a rooted tree on the vertices $0, \ldots, n$
  with root $0$ is recorded by its parent map, the parent of every non-root vertex having a
  smaller label (every finite rooted tree admits such a labelling); two vertices are adjacent
  when one of them is a non-root vertex and the other one is its parent.
* Section 2 of the source: a subtree of $T$ is the empty subgraph or a connected subgraph
  containing the root; it is identified with its vertex set, and a vertex set containing the root
  is connected exactly when it contains the parent of each of its non-root vertices. A subtree is
  admissible if it is empty, or contains the root but none of the leaves of $T$. The boundary
  $\partial S$ is the set of vertices adjacent to $S$ but not in $S$, with the convention
  $\partial\emptyset = \{\text{root}\}$.
* Definition 2 of the source: $A_T(x, y) = \sum_{T'} x^{|T'|} y^{|\partial T'|}$, the sum being
  over the admissible subtrees $T'$ of $T$. It is a polynomial in the variables `X 0` (for $x$)
  and `X 1` (for $y$).
* `main` is the result that the abstract announces: $A$ is not complete, that is, there are
  non-isomorphic rooted trees with the same polynomial $A$ (Remark 16 of the source). The
  abstract also says that the same question remains open for the invariant $M$; nothing about
  $M$ is asserted here.
-/

namespace OMA.S_arxiv_2302_08394

/-- A rooted tree on the vertices `0, …, n` with root `0`, recorded by its parent map. -/
structure RootedTree (n : ℕ) where
  parent : Fin (n + 1) → Fin (n + 1)
  parent_lt : ∀ v, v ≠ 0 → parent v < v

namespace RootedTree

variable {n : ℕ} (T : RootedTree n)

/-- Adjacency in the tree: one vertex is a non-root vertex and the other one is its parent. -/
def Adj (v w : Fin (n + 1)) : Prop :=
  (v ≠ 0 ∧ T.parent v = w) ∨ (w ≠ 0 ∧ T.parent w = v)

instance : DecidableRel T.Adj := fun v w =>
  inferInstanceAs (Decidable ((v ≠ 0 ∧ T.parent v = w) ∨ (w ≠ 0 ∧ T.parent w = v)))

/-- A leaf is a vertex without children. -/
def IsLeaf (v : Fin (n + 1)) : Prop := ∀ w, w ≠ 0 → T.parent w ≠ v

instance : DecidablePred T.IsLeaf := fun v =>
  inferInstanceAs (Decidable (∀ w, w ≠ 0 → T.parent w ≠ v))

/-- Admissible subtrees, as vertex sets: the empty set, and the sets that contain the root, are
connected (they contain the parent of each of their non-root vertices) and contain no leaf. -/
def IsAdmissible (S : Finset (Fin (n + 1))) : Prop :=
  S = ∅ ∨ (0 ∈ S ∧ (∀ v ∈ S, v ≠ 0 → T.parent v ∈ S) ∧ ∀ v ∈ S, ¬ T.IsLeaf v)

instance : DecidablePred T.IsAdmissible := fun S =>
  inferInstanceAs (Decidable
    (S = ∅ ∨ (0 ∈ S ∧ (∀ v ∈ S, v ≠ 0 → T.parent v ∈ S) ∧ ∀ v ∈ S, ¬ T.IsLeaf v)))

/-- The number of boundary vertices of `S`: the vertices adjacent to `S` but not in `S`, with
the convention that the boundary of the empty set is the root. -/
def boundaryCard (S : Finset (Fin (n + 1))) : ℕ :=
  if S = ∅ then 1 else (Finset.univ.filter (fun w => w ∉ S ∧ ∃ v ∈ S, T.Adj v w)).card

/-- The polynomial `A_T(x, y)` of Definition 2, with `x = X 0` and `y = X 1`. -/
noncomputable def A : MvPolynomial (Fin 2) ℤ :=
  ∑ S ∈ Finset.univ.filter T.IsAdmissible,
    MvPolynomial.X 0 ^ S.card * MvPolynomial.X 1 ^ T.boundaryCard S

/-- Isomorphism of rooted trees: a graph isomorphism that maps the root to the root. -/
def Isomorphic (T₁ T₂ : RootedTree n) : Prop :=
  ∃ σ : Equiv.Perm (Fin (n + 1)), σ 0 = 0 ∧ ∀ v w, T₁.Adj v w ↔ T₂.Adj (σ v) (σ w)

end RootedTree

theorem main : ∃ (n : ℕ) (T₁ T₂ : RootedTree n), ¬ T₁.Isomorphic T₂ ∧ T₁.A = T₂.A := by
  sorry

end OMA.S_arxiv_2302_08394
