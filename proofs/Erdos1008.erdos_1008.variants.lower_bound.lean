import FormalConjectures.ErdosProblems.«1008»

open SimpleGraph

theorem OMA.solution : type_of% @Erdos1008.erdos_1008.variants.lower_bound := by
  classical
  refine ⟨1 / 2, by norm_num, fun V _ G => ?_⟩
  obtain ⟨F, _, hF⟩ := G.exists_maximal_isAcyclic_of_le_isAcyclic bot_le isAcyclic_bot
  refine ⟨F, hF.1.1, isAcyclic_iff_free_cycleGraph.1 hF.1.2 4 (by decide), ?_⟩
  have hsup : G.support ⊆ F.support := fun v hv => by
    obtain ⟨w, hw⟩ := G.mem_support.1 hv
    exact (F.degree_pos_iff_mem_support v).1
      ((G.reachable_eq_of_maximal_isAcyclic F hF ▸ hw.reachable).degree_pos_left hw.ne)
  have hvert : Fintype.card F.support ≤ 2 * F.edgeFinset.card := by
    rw [← F.sum_degrees_support_eq_twice_card_edges, ← Set.toFinset_card F.support]
    exact (Finset.card_eq_sum_ones _).le.trans <| Finset.sum_le_sum fun v hv =>
      (F.degree_pos_iff_mem_support v).2 (Set.mem_toFinset.1 hv)
  have hedge : G.edgeFinset.card ≤ (2 * F.edgeFinset.card) ^ 2 := by
    rw [← G.card_edgeFinset_induce_of_support_subset hsup]
    exact ((G.induce F.support).card_edgeFinset_le_card_choose_two.trans
      (Nat.choose_le_pow _ _)).trans (Nat.pow_le_pow_left hvert _)
  rw [← Real.sqrt_eq_rpow]
  have hsq : Real.sqrt G.edgeSet.ncard ≤ 2 * F.edgeSet.ncard := (Real.sqrt_le_left (by positivity)).2 <| by
    rw [Set.ncard_eq_toFinset_card', Set.ncard_eq_toFinset_card']; exact_mod_cast hedge
  linarith
