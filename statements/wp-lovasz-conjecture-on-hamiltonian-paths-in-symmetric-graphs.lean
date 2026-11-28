import Mathlib

/-!
# Lovász conjecture on Hamiltonian paths in symmetric graphs

Source: https://en.wikipedia.org/wiki/Lovász_conjecture
Credit: @ihateSAS

The Lovász conjecture (1969) says:

  Every finite connected vertex-transitive graph contains a Hamiltonian path.

A graph is vertex-transitive when any vertex can be mapped to any other by a graph automorphism,
and a Hamiltonian path is a walk that visits every vertex exactly once (Mathlib's
`SimpleGraph.Walk.IsHamiltonian`). `Nonempty V` together with `G.Preconnected` is the usual
meaning of `G` being connected; Mathlib keeps these two conditions separate, so both appear here.
The `DecidableEq V` instance is only what `Walk.IsHamiltonian` needs to count occurrences of a
vertex in the support of the walk.
-/

namespace OMA.S_wp_lovasz_conjecture_on_hamiltonian_paths_in_symmetric_graphs

/-- A graph is vertex-transitive if any vertex can be taken to any other vertex by an
automorphism of the graph. -/
def IsVertexTransitive {V : Type} (G : SimpleGraph V) : Prop :=
  ∀ v w : V, ∃ e : G ≃g G, e v = w

/-- **Lovász conjecture.** Every finite connected vertex-transitive graph has a Hamiltonian
path. -/
theorem main :
    ∀ {V : Type} [Fintype V] [DecidableEq V] (G : SimpleGraph V),
      G.Preconnected → Nonempty V → IsVertexTransitive G →
        ∃ (a b : V) (p : G.Walk a b), p.IsHamiltonian := by
  sorry

end OMA.S_wp_lovasz_conjecture_on_hamiltonian_paths_in_symmetric_graphs
