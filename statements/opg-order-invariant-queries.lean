import Mathlib

/-!
# Order-invariant queries on graphs of bounded tree-width

Source https://www.openproblemgarden.org/op/order_invariant_queries

The first question asks whether every order-invariant first-order
query on finite vertex-colored graphs is first-order definable
without the extra order on each class of bounded tree-width.
-/

namespace OMA.S_opg_order_invariant_queries

open FirstOrder

inductive GraphRelation (colors : ℕ) : ℕ → Type
  | edge : GraphRelation colors 2
  | color (i : Fin colors) : GraphRelation colors 1

inductive OrderedGraphRelation (colors : ℕ) : ℕ → Type
  | graph {arity : ℕ} (r : GraphRelation colors arity) : OrderedGraphRelation colors arity
  | less : OrderedGraphRelation colors 2

def GraphLanguage (colors : ℕ) : Language :=
  ⟨fun _ => Empty, GraphRelation colors⟩

def OrderedGraphLanguage (colors : ℕ) : Language :=
  ⟨fun _ => Empty, OrderedGraphRelation colors⟩

abbrev graphStructure {n colors : ℕ} (G : SimpleGraph (Fin n))
    (labels : Fin colors → Set (Fin n)) : (GraphLanguage colors).Structure (Fin n) where
  funMap f := f.elim
  RelMap
    | .edge, xs => G.Adj (xs 0) (xs 1)
    | .color i, xs => xs 0 ∈ labels i

abbrev orderedGraphStructure {n colors : ℕ} (G : SimpleGraph (Fin n))
    (labels : Fin colors → Set (Fin n)) (order : LinearOrder (Fin n)) :
    (OrderedGraphLanguage colors).Structure (Fin n) where
  funMap f := f.elim
  RelMap
    | .graph r, xs => (graphStructure G labels).RelMap r xs
    | .less, xs => letI := order; xs 0 < xs 1

def HoldsInGraph {n colors : ℕ} (G : SimpleGraph (Fin n))
    (labels : Fin colors → Set (Fin n)) (φ : (GraphLanguage colors).Sentence) : Prop :=
  letI := graphStructure G labels
  Fin n ⊨ φ

def HoldsInOrderedGraph {n colors : ℕ} (G : SimpleGraph (Fin n))
    (labels : Fin colors → Set (Fin n)) (order : LinearOrder (Fin n))
    (φ : (OrderedGraphLanguage colors).Sentence) : Prop :=
  letI := orderedGraphStructure G labels order
  Fin n ⊨ φ

def IsOrderInvariant {colors : ℕ} (φ : (OrderedGraphLanguage colors).Sentence) : Prop :=
  ∀ (n : ℕ) (G : SimpleGraph (Fin n)) (labels : Fin colors → Set (Fin n))
    (o₁ o₂ : LinearOrder (Fin n)),
    HoldsInOrderedGraph G labels o₁ φ ↔ HoldsInOrderedGraph G labels o₂ φ

def HasTreewidthAtMost {n : ℕ} (G : SimpleGraph (Fin n)) (k : ℕ) : Prop :=
  ∃ (m : ℕ) (T : SimpleGraph (Fin m)) (bag : Fin m → Finset (Fin n)),
    T.IsTree ∧ (∀ i, (bag i).card ≤ k + 1) ∧
    (∀ v, ∃ i, v ∈ bag i) ∧
    (∀ v w, G.Adj v w → ∃ i, v ∈ bag i ∧ w ∈ bag i) ∧
    ∀ v, (T.induce {i | v ∈ bag i}).Connected

theorem main :
    ∀ (colors k : ℕ) (φ : (OrderedGraphLanguage colors).Sentence),
      IsOrderInvariant φ →
      ∃ ψ : (GraphLanguage colors).Sentence,
        ∀ (n : ℕ) (G : SimpleGraph (Fin n)) (labels : Fin colors → Set (Fin n)),
          HasTreewidthAtMost G k → ∀ order : LinearOrder (Fin n),
            HoldsInOrderedGraph G labels order φ ↔ HoldsInGraph G labels ψ := by
  sorry

end OMA.S_opg_order_invariant_queries
