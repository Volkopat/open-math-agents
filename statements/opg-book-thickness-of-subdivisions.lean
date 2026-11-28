import Mathlib

/-!
# Book thickness of subdivisions

Source: https://www.openproblemgarden.org/op/book_thickness_of_subdivisions
Credit: @shc261392

Let `G` be a finite simple graph. A `k`-page book embedding of `G` consists of a linear order
`≼` of `V(G)` and a (non-proper) `k`-colouring of `E(G)` such that edges with the same colour do
not cross with respect to `≼`: if `v ≺ x ≺ w ≺ y` for edges `vw, xy`, then `vw` and `xy` receive
distinct colours. The book thickness `bt(G)` is the least `k` with a `k`-page book embedding. Let
`G'` be the graph obtained by subdividing each edge of `G` exactly once.

Conjecture (Blankenship and Oporowski): there is a function `f` such that for every graph `G`,
`bt(G) ≤ f(bt(G'))`.

Reading used here:
* The linear order is given by an injective `σ : V → ℕ`; the colouring by `c : V → V → ℕ` with
  values below `k` on edges, where only the values `c v w` with `σ v < σ w` on edges `vw` matter.
* `G'` has vertex type `V ⊕ G.edgeSet`, the subdivision vertex of edge `e` being adjacent to the
  two ends of `e`.
* The conjecture is stated as: there is `f : ℕ → ℕ` such that whenever `G'` has a `k`-page book
  embedding, `G` has an `f k`-page book embedding (equivalent to the source form, taking `f`
  monotone).
-/

namespace OMA.S_opg_book_thickness_of_subdivisions

/-- `G` has a `k`-page book embedding. -/
def HasBookEmbedding {V : Type} (G : SimpleGraph V) (k : ℕ) : Prop :=
  ∃ σ : V → ℕ, Function.Injective σ ∧ ∃ c : V → V → ℕ, (∀ v w, G.Adj v w → c v w < k) ∧
    ∀ v w x y, G.Adj v w → G.Adj x y → σ v < σ x → σ x < σ w → σ w < σ y → c v w ≠ c x y

/-- The 1-subdivision `G'` of `G`. -/
def subdivision {V : Type} (G : SimpleGraph V) : SimpleGraph (V ⊕ G.edgeSet) :=
  SimpleGraph.fromRel fun a b => ∃ (v : V) (e : G.edgeSet), a = Sum.inl v ∧ b = Sum.inr e ∧
    v ∈ (e : Sym2 V)

theorem main :
    ∃ f : ℕ → ℕ, ∀ (V : Type) [Fintype V] (G : SimpleGraph V) (k : ℕ),
      HasBookEmbedding (subdivision G) k → HasBookEmbedding G (f k) := by
  sorry

end OMA.S_opg_book_thickness_of_subdivisions
