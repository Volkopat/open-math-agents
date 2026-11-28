import Mathlib

/-!
# Characterizing (aleph_0,aleph_1)-graphs

Source: https://www.openproblemgarden.org/op/characterizing_aleph_0_aleph_1_graphs
-- Credit: @Dugongue (agent: Claude Code, model claude-opus-5-5)

The page asks to characterize the `(ℵ₀,ℵ₁)`-graphs and then poses the concrete question of
Diestel and Leader: does every `(ℵ₀,ℵ₁)`-graph have an `(ℵ₀,ℵ₁)`-graph minor which is either
indivisible or of binary type? Diestel and Leader suspect the answer is no; `main` states that
answer (some `(ℵ₀,ℵ₁)`-graph has no such minor). A proof of the negation answers yes.

Conventions:
* `(ℵ₀,ℵ₁)`-graph, as in Diestel–Leader (J. London Math. Soc. 63 (2001)): a bipartite graph
  with bipartition `(A, B)`, `|A| = ℵ₀`, `|B| = ℵ₁`, every vertex of `B` of infinite degree.
  (The page's wording assigns the cardinals to degrees; the source paper's definition is used.)
* Divisible: there are disjoint `A', A'' ⊆ A` and disjoint `B', B'' ⊆ B` such that the graphs
  induced on `A' ∪ B'` and on `A'' ∪ B''` are `(ℵ₀,ℵ₁)`-graphs with bipartitions `(A', B')`
  and `(A'', B'')`.
* Binary type: isomorphic to a subgraph of the graph on `V(T) ⊔ X`, `T` the infinite rooted
  binary tree (vertices = finite `Bool` words), `X` its rays from the root (`ℕ → Bool`), a word
  adjacent to a ray iff it lies on it (is a prefix of it).
* Minor (arbitrary graphs): disjoint nonempty connected branch sets, one per vertex of the minor,
  with an edge between the branch sets of any two adjacent vertices.
-/

namespace OMA.S_opg_characterizing_aleph_0_aleph_1_graphs

open Cardinal

/-- `G` is an `(ℵ₀,ℵ₁)`-graph with bipartition `(A, B)`. -/
def IsA0A1With {V : Type} (G : SimpleGraph V) (A B : Set V) : Prop :=
  Disjoint A B ∧ A ∪ B = Set.univ ∧ (∀ u v, G.Adj u v → (u ∈ A ↔ v ∈ B)) ∧
    #A = ℵ₀ ∧ #B = ℵ₁ ∧ ∀ b ∈ B, (G.neighborSet b).Infinite

/-- `G` is an `(ℵ₀,ℵ₁)`-graph. -/
def IsA0A1 {V : Type} (G : SimpleGraph V) : Prop :=
  ∃ A B : Set V, IsA0A1With G A B

/-- The induced graph on `S`, with `(A', B')` viewed inside `S`. -/
def InducedA0A1 {V : Type} (G : SimpleGraph V) (A' B' : Set V) : Prop :=
  IsA0A1With (G.induce (A' ∪ B')) {x | x.1 ∈ A'} {x | x.1 ∈ B'}

/-- `G` is divisible (for some bipartition witnessing that it is an `(ℵ₀,ℵ₁)`-graph). -/
def Divisible {V : Type} (G : SimpleGraph V) : Prop :=
  ∃ A B : Set V, IsA0A1With G A B ∧
    ∃ A' A'' B' B'' : Set V, A' ⊆ A ∧ A'' ⊆ A ∧ B' ⊆ B ∧ B'' ⊆ B ∧
      Disjoint A' A'' ∧ Disjoint B' B'' ∧ InducedA0A1 G A' B' ∧ InducedA0A1 G A'' B''

/-- The tree–ray graph: a finite word is adjacent to a ray iff it is a prefix of the ray. -/
def treeRay : SimpleGraph (List Bool ⊕ (ℕ → Bool)) :=
  SimpleGraph.fromRel fun p q =>
    match p, q with
    | Sum.inl w, Sum.inr x => ∀ i : Fin w.length, w.get i = x i
    | _, _ => False

/-- `G` is isomorphic to a subgraph of the tree–ray graph. -/
def BinaryType {V : Type} (G : SimpleGraph V) : Prop :=
  ∃ f : V → List Bool ⊕ (ℕ → Bool), Function.Injective f ∧ ∀ u v, G.Adj u v → treeRay.Adj (f u) (f v)

/-- `H` is a minor of `G`. -/
def IsMinor {V W : Type} (H : SimpleGraph W) (G : SimpleGraph V) : Prop :=
  ∃ br : W → Set V, (∀ w, (br w).Nonempty) ∧ (∀ w w', w ≠ w' → Disjoint (br w) (br w')) ∧
    (∀ w, (G.induce (br w)).Connected) ∧
    ∀ w w', H.Adj w w' → ∃ a ∈ br w, ∃ b ∈ br w', G.Adj a b

/-- Expected (negative) answer to the Diestel–Leader question. -/
theorem main :
    ∃ (V : Type) (G : SimpleGraph V), IsA0A1 G ∧
      ∀ (W : Type) (H : SimpleGraph W), IsMinor H G → IsA0A1 H →
        Divisible H ∧ ¬ BinaryType H := by
  sorry

end OMA.S_opg_characterizing_aleph_0_aleph_1_graphs
