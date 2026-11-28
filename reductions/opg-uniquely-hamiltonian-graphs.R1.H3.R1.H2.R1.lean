import OMAReductions.R_opg_uniquely_hamiltonian_graphs_R1_H3_R1

-- A perfect matching in the bipartite graph outside the given cycle
-- leaves a spanning cubic graph containing that cycle.

namespace OMA.R_opg_uniquely_hamiltonian_graphs_R1_H3_R1_H2_R1

open SimpleGraph OMA.S_opg_uniquely_hamiltonian_graphs

def H1 : Prop :=
  ∀ (V : Type) [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj],
    G.IsBipartite → G.IsRegularOfDegree 4 →
      ∀ (v : V) (c : G.Walk v v), IsHamiltonCycle G c →
        ∃ K : SimpleGraph V, ∃ decK : DecidableRel K.Adj,
          letI := decK
          K ≤ G ∧ K.IsRegularOfDegree 3 ∧
            ∃ cK : K.Walk v v, IsHamiltonCycle K cK ∧
              cK.edges.toFinset = c.edges.toFinset

def H2 : Prop :=
  ∀ (V : Type) [Fintype V] [DecidableEq V] (K : SimpleGraph V) [DecidableRel K.Adj],
    K.IsRegularOfDegree 3 →
      ∀ (v : V) (c : K.Walk v v), IsHamiltonCycle K c →
        ∃ (w : V) (d : K.Walk w w), IsHamiltonCycle K d ∧
          d.edges.toFinset ≠ c.edges.toFinset

theorem main : H1 → H2 → OMA.R_opg_uniquely_hamiltonian_graphs_R1_H3_R1.H2 := by
  classical
  intro extract second V _ _ G _ hBip hRegular v c hCycle
  obtain ⟨K, decK, hKG, hCubic, cK, hcK, hSame⟩ := extract V G hBip hRegular v c hCycle
  letI := decK
  obtain ⟨w, d, hd, hDistinct⟩ := second V K hCubic v cK hcK
  refine ⟨w, d.mapLe hKG, ⟨(Walk.isCycle_mapLe hKG).2 hd.1, ?_⟩, ?_⟩
  · simpa only [Walk.support_mapLe_eq_support] using hd.2
  · simpa only [Walk.edges_mapLe_eq_edges, hSame] using hDistinct

end OMA.R_opg_uniquely_hamiltonian_graphs_R1_H3_R1_H2_R1

