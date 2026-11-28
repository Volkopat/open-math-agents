import OMAReductions.R_opg_uniquely_hamiltonian_graphs_R1_H3_R1_H2_R1

/-!
Remove the spanning Hamilton cycle from the 4-regular bipartite graph. The residual
is 2-regular; double-counting verifies Hall's condition, giving a perfect matching.
Adding the matching to the cycle gives a spanning cubic graph with the same cycle edges.
-/

namespace OMA.HamiltonCubic

open Finset SimpleGraph
open scoped BigOperators

theorem exists_perfect_matching_of_regular_bipartite
    {V : Type*} [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj]
    (k : ℕ) (hk : 0 < k) (hreg : G.IsRegularOfDegree k) (hbip : G.IsBipartite) :
    ∃ M : G.Subgraph, M.IsPerfectMatching := by
  classical
  obtain ⟨p₁, p₂, hb⟩ := hbip.exists_isBipartiteWith
  refine exists_isPerfectMatching_of_forall_ncard_le hb ?_
  intro s
  let S := s.toFinset
  let N := S.biUnion fun v => G.neighborFinset v
  have hN : (N : Set V) = ⋃ x ∈ s, G.neighborSet x := by
    ext y
    simp [N, S]
  have hRowCount (T : Finset V) (v : V) :
      (∑ w ∈ T, if G.Adj v w then (1 : ℕ) else 0) = (T.filter (G.Adj v)).card := by
    rw [← Finset.sum_filter]
    simp
  have hRow (v : V) (hv : v ∈ S) : N.filter (G.Adj v) = G.neighborFinset v := by
    ext w
    constructor
    · exact fun hw => (G.mem_neighborFinset v w).mpr (mem_filter.mp hw).2
    · intro hw
      exact mem_filter.mpr ⟨mem_biUnion.mpr ⟨v, hv, hw⟩, (G.mem_neighborFinset v w).mp hw⟩
  have hCol (w : V) : S.filter (G.Adj w) ⊆ G.neighborFinset w :=
    fun x hx => (G.mem_neighborFinset w x).mpr (mem_filter.mp hx).2
  have hdeg (v : V) : (G.neighborFinset v).card = k :=
    (G.card_neighborFinset_eq_degree v).trans (hreg.degree_eq v)
  have hcounts : S.card * k ≤ N.card * k := by
    calc
      S.card * k = ∑ _v ∈ S, k := by simp
      _ = ∑ v ∈ S, ∑ w ∈ N, if G.Adj v w then (1 : ℕ) else 0 := by
        apply sum_congr rfl
        intro v hv
        rw [hRowCount, hRow v hv, hdeg]
      _ = ∑ w ∈ N, ∑ v ∈ S, if G.Adj v w then (1 : ℕ) else 0 := sum_comm
      _ = ∑ w ∈ N, ∑ v ∈ S, if G.Adj w v then (1 : ℕ) else 0 := by
        apply sum_congr rfl
        intro w _
        apply sum_congr rfl
        intro v _
        by_cases hadj : G.Adj v w
        · simp only [if_pos hadj, if_pos hadj.symm]
        · have hrev : ¬ G.Adj w v := fun h => hadj h.symm
          simp only [if_neg hadj, if_neg hrev]
      _ ≤ ∑ _w ∈ N, k := by
        apply sum_le_sum
        intro w _
        rw [hRowCount, ← hdeg w]
        exact card_le_card (hCol w)
      _ = N.card * k := by simp
  rw [Set.ncard_eq_toFinset_card' s, ← hN, Set.ncard_coe_finset]
  exact Nat.le_of_mul_le_mul_right hcounts hk

theorem exists_cubic_spanning_cycle {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (hbip : G.IsBipartite)
    (hreg : G.IsRegularOfDegree 4) (v : V) (c : G.Walk v v)
    (hcycle : c.IsCycle) (hspan : ∀ w : V, w ∈ c.support)
    (hHall : ∀ (D : SimpleGraph V) [DecidableRel D.Adj],
      D.IsRegularOfDegree 2 → D.IsBipartite → ∃ M : D.Subgraph, M.IsPerfectMatching) :
    ∃ K : SimpleGraph V, ∃ decK : DecidableRel K.Adj,
      letI := decK
      K ≤ G ∧ K.IsRegularOfDegree 3 ∧ ∃ q : K.Walk v v,
        (q.IsCycle ∧ ∀ w : V, w ∈ q.support) ∧ q.edges.toFinset = c.edges.toFinset := by
  let C : SimpleGraph V := c.toSubgraph.spanningCoe
  let _ : DecidableRel C.Adj := Classical.decRel _
  let D : SimpleGraph V := G \ C
  let _ : DecidableRel D.Adj := Classical.decRel _
  have hCG : C ≤ G := c.toSubgraph.spanningCoe_le
  have hDG : D ≤ G := sdiff_le
  have hC2 (w : V) : C.degree w = 2 := by
    rw [SimpleGraph.degree, ← Set.ncard_coe_finset, C.coe_neighborFinset]
    exact hcycle.ncard_neighborSet_toSubgraph_eq_two (hspan w)
  have hD2 : D.IsRegularOfDegree 2 := by
    intro w
    have hsub : C.neighborFinset w ⊆ G.neighborFinset w := by
      intro x hx
      exact (G.mem_neighborFinset w x).mpr (hCG ((C.mem_neighborFinset w x).mp hx))
    change ((G \ C).neighborFinset w).card = 2
    rw [neighborFinset_sdiff, Finset.card_sdiff_of_subset hsub,
      ← SimpleGraph.degree, ← SimpleGraph.degree, hreg.degree_eq w, hC2 w]
  obtain ⟨M, hM⟩ := hHall D hD2 (Colorable.mono_left hDG hbip)
  let P : SimpleGraph V := M.spanningCoe
  let _ : DecidableRel P.Adj := Classical.decRel _
  let K := C ⊔ P
  let dK : DecidableRel K.Adj := Classical.decRel _
  let _ : DecidableRel K.Adj := dK
  have hPD : P ≤ D := M.spanningCoe_le
  have hKG : K ≤ G := sup_le hCG (hPD.trans hDG)
  have hCK : C ≤ K := le_sup_left
  have hdis : Disjoint C P := by
    rw [SimpleGraph.disjoint_left]
    intro x y hxy hp
    exact (hPD hp).2 hxy
  have hP1 (w : V) : P.degree w = 1 :=
    SimpleGraph.degree_eq_one_iff_existsUnique_adj.mpr (Subgraph.isPerfectMatching_iff.mp hM w)
  have hK3 : K.IsRegularOfDegree 3 := by
    intro w
    change ((C ⊔ P).neighborFinset w).card = 3
    rw [neighborFinset_sup_of_disjoint w hdis, Finset.card_disjUnion,
      ← SimpleGraph.degree, ← SimpleGraph.degree, hC2 w, hP1 w]
  let toK : c.toSubgraph.coe →g K :=
    ⟨Subtype.val, fun h => hCK h⟩
  let q : K.Walk v v := c.mapToSubgraph.map toK
  have hmap : q.mapLe hKG = c := by
    change (c.mapToSubgraph.map toK).map (Hom.ofLE hKG) = c
    rw [Walk.map_map]
    exact c.map_mapToSubgraph_hom
  have hq : q.IsCycle := Walk.IsCycle.of_mapLe (h := hKG) (by rw [hmap]; exact hcycle)
  have hsupport : q.support = c.support :=
    (q.support_mapLe_eq_support hKG).symm.trans (congrArg Walk.support hmap)
  have hedges : q.edges = c.edges :=
    (q.edges_mapLe_eq_edges hKG).symm.trans (congrArg Walk.edges hmap)
  exact ⟨K, dK, hKG, hK3, q, ⟨hq, fun w => hsupport.symm ▸ hspan w⟩,
    congrArg List.toFinset hedges⟩

end OMA.HamiltonCubic

theorem OMA.solution : OMA.R_opg_uniquely_hamiltonian_graphs_R1_H3_R1_H2_R1.H1 := by
  intro V _ _ G _ hbip hreg v c hc
  exact OMA.HamiltonCubic.exists_cubic_spanning_cycle G hbip hreg v c hc.1 hc.2
    (fun D _ hd hb => OMA.HamiltonCubic.exists_perfect_matching_of_regular_bipartite
      D 2 (by decide) hd hb)
