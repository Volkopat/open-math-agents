import Mathlib

/-!
# Two-colouring the edges so that large induced subgraphs are not monochromatic

Source: https://mathoverflow.net/questions/330734
Credit: @jagraj28

The question: can we colour the edges of any graph `G` on `2m - 1` vertices with two colours so
that every induced subgraph with at least `m` edges is non-monochromatic? If true, this is sharp:
in any two-colouring of the star `K_{1,2m-1}` (on `2m` vertices) some colour has at least `m`
edges, and the subgraph induced by the centre and those leaves is monochromatic.

The question has no answer. `main` states a positive answer. An exhaustive search confirms it
for `m ≤ 3` (all graphs on at most 5 vertices).

Conventions.
* `m ≥ 1`, and graphs are `SimpleGraph (Fin (2 * m - 1))`.
* A two-colouring of the edges is a function `c : Sym2 (Fin (2 * m - 1)) → Bool`; only its values
  on edges of `G` matter.
* The edges of the induced subgraph on `S` are the edges of `G` with both ends in `S`.
* "Non-monochromatic" means that two of these edges have different colours.
-/

namespace OMA.S_mo_330734

/-- The edges of `G` with both endpoints in `S`, that is, the edges of the induced subgraph
`G[S]`. -/
def inducedEdges {V : Type} [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj]
    (S : Finset V) : Finset (Sym2 V) :=
  G.edgeFinset.filter fun e => ∀ v ∈ e, v ∈ S

/-- Every graph on `2m - 1` vertices has a two-colouring of its edges in which every induced
subgraph with at least `m` edges uses both colours. -/
theorem main : ∀ m : ℕ, 1 ≤ m → ∀ (G : SimpleGraph (Fin (2 * m - 1))) [DecidableRel G.Adj],
    ∃ c : Sym2 (Fin (2 * m - 1)) → Bool, ∀ S : Finset (Fin (2 * m - 1)),
      m ≤ (inducedEdges G S).card →
        ∃ e₁ ∈ inducedEdges G S, ∃ e₂ ∈ inducedEdges G S, c e₁ ≠ c e₂ := by
  sorry

end OMA.S_mo_330734
