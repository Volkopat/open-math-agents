import Mathlib

/-!
# Switching reconstruction conjecture

Source: https://www.openproblemgarden.org/op/switching_reconstruction_conjecture
Credit: @ishaanzee

**Conjecture** (R. P. Stanley). Every simple graph on five or more vertices is
switching-reconstructible.

To switch a vertex of a simple graph is to exchange its sets of neighbours and non-neighbours.
The graph so obtained is called a switching of the graph. The collection of switchings of a graph
`G` is called the switching deck of `G`. A graph is switching-reconstructible if every graph with
the same deck as `G` is isomorphic to `G`. (There are four pairs of non-isomorphic graphs on four
vertices with the same deck, so five vertices is the right threshold.)

Formalization:
* Graphs are finite simple graphs. `switch G v` toggles the adjacency of `v` with every other
  vertex and leaves all other pairs unchanged.
* The deck is a multiset of graphs up to isomorphism, so `G` and `H` (necessarily with the same
  number of vertices, hence on the same vertex type `V`) have the same deck iff there is a
  bijection `σ` of the vertices with `switch G v ≅ switch H (σ v)` for every `v`.
-/

namespace OMA.S_opg_switching_reconstruction_conjecture

/-- The switching of `G` at `v`: exchange the neighbours and non-neighbours of `v`. -/
def switch {V : Type*} [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj] (v : V) :
    SimpleGraph V :=
  SimpleGraph.fromRel fun x y => if x = v ∨ y = v then ¬ G.Adj x y else G.Adj x y

/-- **Stanley's switching reconstruction conjecture**: two graphs on at least five vertices with
the same switching deck are isomorphic. -/
theorem main : ∀ (V : Type) [Fintype V] [DecidableEq V] (G H : SimpleGraph V)
    [DecidableRel G.Adj] [DecidableRel H.Adj], 5 ≤ Fintype.card V →
    (∃ σ : V ≃ V, ∀ v : V, Nonempty (switch G v ≃g switch H (σ v))) → Nonempty (G ≃g H) := by
  sorry

end OMA.S_opg_switching_reconstruction_conjecture
