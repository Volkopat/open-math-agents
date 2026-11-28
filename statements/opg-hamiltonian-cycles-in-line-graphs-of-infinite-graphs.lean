import Mathlib

/-!
# Hamiltonian circles in locally finite line graphs

The two assertions concern four-edge-connectivity of the root graph and
four-vertex-connectivity of its line graph, respectively. In both cases
the conclusion is a Hamiltonian circle in the line graph.

[Open Problem Garden](https://www.openproblemgarden.org/op/hamiltonian_cycles_in_line_graphs_of_infinite_graphs)
[Mohar, Conjectures 3 and 4](https://www.sfu.ca/~mohar/Problems/P0703_HamiltonicityInfinite.html)
-/

namespace OMA.S_opg_hamiltonian_cycles_in_line_graphs_of_infinite_graphs

def edgeCut {V : Type*} (G : SimpleGraph V) (S : Set V) : Set (Sym2 V) :=
  {e ∈ G.edgeSet | ∃ x ∈ S, ∃ y ∉ S, e = s(x, y)}

def InCycleSpace {V : Type*} (G : SimpleGraph V) (F : Set (Sym2 V)) : Prop :=
  F ⊆ G.edgeSet ∧
    ∀ S : Set V, (edgeCut G S).Finite → Even ((F ∩ edgeCut G S).ncard)

def HasHamiltonianCircle {V : Type*} (G : SimpleGraph V) : Prop :=
  ∃ F : Set (Sym2 V), F.Nonempty ∧ InCycleSpace G F ∧
    (∀ H ⊆ F, H.Nonempty → InCycleSpace G H → H = F) ∧
    ∀ x : V, ∃ y : V, s(x, y) ∈ F

def IsFourEdgeConnected {V : Type*} (G : SimpleGraph V) : Prop :=
  Nontrivial V ∧
    ∀ S : Set V, S.Nonempty → Sᶜ.Nonempty → 4 ≤ (edgeCut G S).encard

def IsFourVertexConnected {V : Type*} (G : SimpleGraph V) : Prop :=
  Nonempty (Fin 5 ↪ V) ∧
    ∀ S : Finset V, S.card < 4 → (G.induce (S : Set V)ᶜ).Connected

theorem main :
    ∀ (V : Type) (G : SimpleGraph V),
      (∀ v : V, (G.neighborSet v).Finite) →
      (IsFourEdgeConnected G → HasHamiltonianCircle G.lineGraph) ∧
      (IsFourVertexConnected G.lineGraph → HasHamiltonianCircle G.lineGraph) := by
  sorry

end OMA.S_opg_hamiltonian_cycles_in_line_graphs_of_infinite_graphs
