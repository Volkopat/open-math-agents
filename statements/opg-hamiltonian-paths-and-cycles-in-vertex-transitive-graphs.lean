import Mathlib

/-!
# Hamiltonian paths and cycles in vertex transitive graphs

Source: https://www.openproblemgarden.org/op/hamiltonian_paths_and_cycles_in_vertex_transitive_graphs
Credit: @joshuadc11

Lovász's problem: does every finite connected vertex-transitive graph have a Hamiltonian path?

## Encoding

* Graphs are finite Mathlib `SimpleGraph`s; connected is `G.Connected`.
* Vertex-transitivity: for every pair of vertices `u v : V`, there is a graph automorphism
  `f : G ≃g G` with `f u = v`.
* A Hamiltonian path is a walk `p : G.Walk u v` satisfying Mathlib's `p.IsHamiltonian` (every
  vertex of `V` appears in `p.support` exactly once).
* The source asks a yes/no question without conjecturing an answer; `main` states the answer yes,
  and a disproof would answer no.
-/

namespace OMA.S_opg_hamiltonian_paths_and_cycles_in_vertex_transitive_graphs

/-- A graph `G` is vertex-transitive if its automorphism group acts transitively on `V`. -/
def IsVertexTransitive {V : Type} (G : SimpleGraph V) : Prop :=
  ∀ u v : V, ∃ f : G ≃g G, f u = v

/-- Every finite connected vertex-transitive graph has a Hamiltonian path. -/
theorem main : ∀ (V : Type) [Fintype V] [DecidableEq V] (G : SimpleGraph V),
    G.Connected → IsVertexTransitive G →
    ∃ (u v : V) (p : G.Walk u v), p.IsHamiltonian := by
  sorry

end OMA.S_opg_hamiltonian_paths_and_cycles_in_vertex_transitive_graphs
