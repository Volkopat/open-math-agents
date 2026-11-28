import OMAReductions.R_opg_uniquely_hamiltonian_graphs_R1

-- Reduction opg-uniquely-hamiltonian-graphs.R1.H4.R1 of step opg-uniquely-hamiltonian-graphs.R1.H4
-- Credit: @hiattco

namespace OMA.R_opg_uniquely_hamiltonian_graphs_R1_H4_R1

open SimpleGraph OMA.S_opg_uniquely_hamiltonian_graphs
open scoped Classical

lemma ham_on_smaller {V : Type*} {G H : SimpleGraph V} {v : V} {c : G.Walk v v}
    (hc : IsHamiltonCycle G c) (keep : ∀ e, e ∈ c.edges → e ∈ H.edgeSet) :
    IsHamiltonCycle H (c.transfer H keep) :=
  ⟨hc.1.transfer keep, fun x => by simpa only [Walk.support_transfer] using hc.2 x⟩

lemma ham_on_larger {V : Type*} {G H : SimpleGraph V} (h : H ≤ G)
    {v : V} {c : H.Walk v v} (hc : IsHamiltonCycle H c) :
    IsHamiltonCycle G (c.mapLe h) :=
  ⟨(Walk.isCycle_mapLe h).mpr hc.1,
    fun x => by simpa only [Walk.support_mapLe_eq_support] using hc.2 x⟩

lemma lift_second_cycle {V : Type*} [DecidableEq V] {G H : SimpleGraph V}
    (h : H ≤ G) {v : V} (c : G.Walk v v)
    (keep : ∀ e, e ∈ c.edges → e ∈ H.edgeSet)
    (second : ∃ (w : V) (d : H.Walk w w), IsHamiltonCycle H d ∧
      d.edges.toFinset ≠ (c.transfer H keep).edges.toFinset) :
    ∃ (w : V) (d : G.Walk w w), IsHamiltonCycle G d ∧
      d.edges.toFinset ≠ c.edges.toFinset := by
  obtain ⟨w, d, hd, hne⟩ := second
  refine ⟨w, d.mapLe h, ham_on_larger h hd, ?_⟩
  simpa only [Walk.edges_mapLe_eq_edges, Walk.edges_transfer] using hne

/-- A spanning quartic subgraph can keep all edges of the prescribed cycle.
The classical construction takes a spanning 2-factor after removing the cycle. -/
def H1 : Prop :=
  ∀ (V : Type) [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj]
    (r : ℕ), Even r → 6 ≤ r → r < 300 → G.IsRegularOfDegree r →
      ∀ (v : V) (c : G.Walk v v), IsHamiltonCycle G c →
        ∃ H : SimpleGraph V, H ≤ G ∧ H.IsRegularOfDegree 4 ∧
          ∀ e, e ∈ c.edges → e ∈ H.edgeSet

/-- The quartic Sheehan conjecture, as in the parent reduction. -/
def H2 : Prop :=
  ∀ (V : Type) [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj],
    G.IsRegularOfDegree 4 →
      ∀ (v : V) (c : G.Walk v v), IsHamiltonCycle G c →
        ∃ (w : V) (d : G.Walk w w), IsHamiltonCycle G d ∧
          d.edges.toFinset ≠ c.edges.toFinset

theorem main : H1 → H2 → OMA.R_opg_uniquely_hamiltonian_graphs_R1.H4 := by
  intro factor quartic V _ _ G _ r he hr hmax hreg v c hc
  obtain ⟨H, hle, hfour, keep⟩ := factor V G r he hr hmax hreg v c hc
  exact lift_second_cycle hle c keep
    (quartic V H hfour v (c.transfer H keep) (ham_on_smaller hc keep))

end OMA.R_opg_uniquely_hamiltonian_graphs_R1_H4_R1
