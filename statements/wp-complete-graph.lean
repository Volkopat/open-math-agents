import Mathlib

/-!
# Gurvich's Δ-conjecture

Source: https://en.wikipedia.org/wiki/List_of_unsolved_problems_in_mathematics
(catalogue entry: https://en.wikipedia.org/wiki/complete_graph)
Credit: @shc261392

Δ-conjecture (Gurvich, 1978). Consider a complete graph `(V; E_1, …, E_d)` each edge of which is
colored by one of `d` colors such that there exists a triangle `Δ` colored in three pairwise
distinct colors. Then, in each chromatic component `(V, E_i)`, `i = 1, …, d`, one can choose a
maximal independent vertex-set such that the intersection of the obtained `d` sets is empty.

Reading used here:
* `V` is a finite vertex set; the colouring is `c : Sym2 V → Fin d`, read on the edges `s(u, v)`
  with `u ≠ v` (its values on the diagonal are ignored).
* The chromatic component `(V, E_i)` is the simple graph on `V` whose edges are those of
  colour `i`.
* A maximal independent set of a graph is an independent set to which no further vertex can be
  added, i.e. every vertex outside it has a neighbour inside it.
-/

namespace OMA.S_wp_complete_graph

/-- The chromatic component of colour `i`. -/
def comp {V : Type} {d : ℕ} (c : Sym2 V → Fin d) (i : Fin d) : SimpleGraph V :=
  SimpleGraph.fromRel fun u v => c s(u, v) = i

/-- `S` is a maximal independent set of `G`. -/
def IsMaxIndep {V : Type} (G : SimpleGraph V) (S : Set V) : Prop :=
  (∀ u ∈ S, ∀ v ∈ S, ¬ G.Adj u v) ∧ ∀ x ∉ S, ∃ y ∈ S, G.Adj x y

theorem main :
    ∀ (V : Type) [Fintype V] (d : ℕ) (c : Sym2 V → Fin d),
      (∃ a b e : V, a ≠ b ∧ b ≠ e ∧ a ≠ e ∧
        c s(a, b) ≠ c s(b, e) ∧ c s(b, e) ≠ c s(a, e) ∧ c s(a, b) ≠ c s(a, e)) →
      ∃ S : Fin d → Set V, (∀ i, IsMaxIndep (comp c i) (S i)) ∧ (⋂ i, S i) = ∅ := by
  sorry

end OMA.S_wp_complete_graph
