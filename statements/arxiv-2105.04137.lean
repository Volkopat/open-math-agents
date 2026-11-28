import Mathlib

/-!
# The dijoin conjecture for the inversion number of oriented graphs

Source: https://arxiv.org/abs/2105.04137 (Jørgen Bang-Jensen, Jonas Costa Ferreira da Silva and
Frédéric Havet, On the inversion number of oriented graphs, DMTCS 23(2), 2022), the conjecture of
the abstract (the dijoin conjecture of Section 1.1).
Credit: @JamesSlash

Definitions of the source (Section 1):
* An oriented graph is a digraph with no loop and no directed cycle of length 2 (no two opposite
  arcs). A digraph is acyclic when it has no directed cycle.
* The inversion of a set `X` of vertices of `D` reverses the direction of every arc with both ends
  in `X`; the other arcs are kept. Inverting a family `X₁, …, X_k` means inverting the sets one
  after another.
* The inversion number `inv(D)` of an oriented graph `D` is the minimum number of inversions needed
  to make `D` acyclic, i.e. the least `k` such that some sets `X₁, …, X_k` make `D` acyclic when
  inverted in turn. For a finite oriented graph such a family always exists (inverting the two ends
  of an arc reverses that arc alone), so the infimum below is a minimum.
* The dijoin `L → R` is the disjoint union of `L` and `R` together with all arcs from `L` to `R`.

The conjecture: for any two oriented graphs `L` and `R`, `inv(L → R) = inv(L) + inv(R)`.
Graphs in the source are finite. Here a digraph is a Mathlib `Digraph` on a finite vertex type;
being oriented is a hypothesis, and a directed cycle is a nontrivial closed directed walk
(`Relation.TransGen` of the arc relation from a vertex back to itself).
-/

namespace OMA.S_arxiv_2105_04137

/-- `D` is an oriented graph: no loop and no two opposite arcs. -/
def IsOriented {V : Type} (D : Digraph V) : Prop :=
  (∀ v, ¬ D.Adj v v) ∧ ∀ u v, D.Adj u v → ¬ D.Adj v u

/-- The inversion of `X` in `D`: the arcs with both ends in `X` are reversed, the others are kept. -/
def invert {V : Type} (D : Digraph V) (X : Set V) : Digraph V where
  Adj u v := (u ∈ X ∧ v ∈ X ∧ D.Adj v u) ∨ (¬ (u ∈ X ∧ v ∈ X) ∧ D.Adj u v)

/-- `D` is acyclic: no vertex can be reached from itself by a nonempty directed walk. -/
def IsAcyclic {V : Type} (D : Digraph V) : Prop :=
  ∀ v, ¬ Relation.TransGen D.Adj v v

/-- The inversion number of `D`: the least `k` such that inverting some sets `X 0, …, X (k - 1)`
one after another makes `D` acyclic. -/
noncomputable def inv {V : Type} (D : Digraph V) : ℕ :=
  sInf {k : ℕ | ∃ X : Fin k → Set V, IsAcyclic ((List.ofFn X).foldl invert D)}

/-- The dijoin `L → R`: disjoint copies of `L` and `R`, together with every arc from `L` to `R`. -/
def dijoin {V W : Type} (L : Digraph V) (R : Digraph W) : Digraph (V ⊕ W) where
  Adj x y := match x, y with
    | .inl a, .inl b => L.Adj a b
    | .inr a, .inr b => R.Adj a b
    | .inl _, .inr _ => True
    | .inr _, .inl _ => False

theorem main : ∀ (V W : Type) [Finite V] [Finite W] (L : Digraph V) (R : Digraph W),
    IsOriented L → IsOriented R → inv (dijoin L R) = inv L + inv R := by
  sorry

end OMA.S_arxiv_2105_04137
