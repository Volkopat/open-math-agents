import Mathlib.Combinatorics.SimpleGraph.Hamiltonian

/-! Source: https://mathoverflow.net/questions/460794 -/

namespace OMA.S_mo_460794

open SimpleGraph

theorem main :
    ∀ (V : Type) [Fintype V] [DecidableEq V] (G : SimpleGraph V)
      (v₀ : V) (C : G.Walk v₀ v₀), C.IsHamiltonianCycle →
      (∀ v, ∃ w, G.Adj v w ∧ s(v, w) ∉ C.edges) →
      ∃ v, ∃ D : G.Walk v v, D.IsCycle ∧
        Fintype.card V < (D.edges.map fun e => if e ∈ C.edges then 1 else 2).sum := by
  sorry

end OMA.S_mo_460794
