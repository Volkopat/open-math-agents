import Mathlib.Combinatorics.SimpleGraph.Hamiltonian
import Mathlib.Combinatorics.SimpleGraph.Matching

/-! Source: Question 2 at https://mathoverflow.net/questions/346399 -/

namespace OMA.S_mo_346399

open SimpleGraph

theorem main :
    ∀ (V : Type) [Fintype V] [DecidableEq V] (G : SimpleGraph V)
      (v₀ : V) (C : G.Walk v₀ v₀) (M N : G.Subgraph),
      C.IsHamiltonianCycle → M.IsPerfectMatching → N.IsPerfectMatching →
      Disjoint M.edgeSet N.edgeSet →
      M.edgeSet ∪ N.edgeSet = G.edgeSet \ {e | e ∈ C.edges} →
      ∃ v, ∃ D : G.Walk v v, D.IsHamiltonianCycle ∧ M.edgeSet ⊆ {e | e ∈ D.edges} := by
  sorry

end OMA.S_mo_346399
