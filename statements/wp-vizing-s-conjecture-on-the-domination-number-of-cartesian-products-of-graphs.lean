import Mathlib

/-!
# Vizing's conjecture on the domination number of Cartesian products of graphs

Source: https://en.wikipedia.org/wiki/Vizing%27s_conjecture
Credit: @ihateSAS

Vizing's conjecture (1968) states that for all finite graphs `G` and `H`,

  `γ(G □ H) ≥ γ(G) * γ(H)`,

where `γ` is the domination number and `□` is the Cartesian product. A set `S` of vertices
dominates a graph when every vertex lies in `S` or is adjacent to a vertex of `S`, and the
domination number is the least cardinality of such a set.
-/

namespace OMA.S_wp_vizing_s_conjecture_on_the_domination_number_of_cartesian_products_of_graphs

/-- A set `S` of vertices dominates `G` if every vertex of `G` lies in `S` or is adjacent to a
vertex of `S`. -/
def IsDominatingSet {V : Type} (G : SimpleGraph V) (S : Set V) : Prop :=
  ∀ v : V, v ∈ S ∨ ∃ s ∈ S, G.Adj v s

/-- The domination number `γ(G)`: the least cardinality of a dominating set of `G`. -/
noncomputable def dominationNumber {V : Type} (G : SimpleGraph V) : ℕ :=
  sInf {n : ℕ | ∃ S : Finset V, S.card = n ∧ IsDominatingSet G (S : Set V)}

/-- **Vizing's conjecture**: the domination number is supermultiplicative over Cartesian
products, `γ(G) * γ(H) ≤ γ(G □ H)`. -/
theorem main :
    ∀ {V W : Type} [Fintype V] [Fintype W] (G : SimpleGraph V) (H : SimpleGraph W),
      dominationNumber G * dominationNumber H ≤ dominationNumber (G □ H) := by
  sorry

end OMA.S_wp_vizing_s_conjecture_on_the_domination_number_of_cartesian_products_of_graphs
