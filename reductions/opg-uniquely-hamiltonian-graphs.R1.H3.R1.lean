import OMAReductions.R_opg_uniquely_hamiltonian_graphs_R1

-- Reduction of step opg-uniquely-hamiltonian-graphs.R1.H3 (the quartic case of
-- Sheehan's conjecture) into three strictly smaller instances.
-- H1 is the verified finite range (all orders at most 21 have been checked).
-- H2 is the bipartite subclass (Thomassen: minimum degree at least three suffices).
-- H3 is the remaining open core: nonbipartite graphs of order at least 22.

namespace OMA.R_opg_uniquely_hamiltonian_graphs_R1_H3_R1

open SimpleGraph OMA.S_opg_uniquely_hamiltonian_graphs

def H1 : Prop :=
  ∀ (V : Type) [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj],
    Fintype.card V ≤ 21 → G.IsRegularOfDegree 4 →
      ∀ (v : V) (c : G.Walk v v), IsHamiltonCycle G c →
        ∃ (w : V) (d : G.Walk w w), IsHamiltonCycle G d ∧
          d.edges.toFinset ≠ c.edges.toFinset

def H2 : Prop :=
  ∀ (V : Type) [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj],
    G.IsBipartite → G.IsRegularOfDegree 4 →
      ∀ (v : V) (c : G.Walk v v), IsHamiltonCycle G c →
        ∃ (w : V) (d : G.Walk w w), IsHamiltonCycle G d ∧
          d.edges.toFinset ≠ c.edges.toFinset

def H3 : Prop :=
  ∀ (V : Type) [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj],
    21 < Fintype.card V → ¬ G.IsBipartite → G.IsRegularOfDegree 4 →
      ∀ (v : V) (c : G.Walk v v), IsHamiltonCycle G c →
        ∃ (w : V) (d : G.Walk w w), IsHamiltonCycle G d ∧
          d.edges.toFinset ≠ c.edges.toFinset

theorem main : H1 → H2 → H3 → OMA.R_opg_uniquely_hamiltonian_graphs_R1.H3 := by
  intro h1 h2 h3 V instV decV G decAdj hreg v c hc
  by_cases hsmall : Fintype.card V ≤ 21
  · exact h1 V G hsmall hreg v c hc
  · have hlarge : 21 < Fintype.card V := by omega
    by_cases hbip : G.IsBipartite
    · exact h2 V G hbip hreg v c hc
    · exact h3 V G hlarge hbip hreg v c hc

end OMA.R_opg_uniquely_hamiltonian_graphs_R1_H3_R1
