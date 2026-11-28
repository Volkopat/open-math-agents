import FormalConjectures.ErdosProblems.«151»

/-! The square-root bound for clique transversals. -/

open SimpleGraph Finset

theorem OMA.solution : type_of% @Erdos151.erdos_151.variants.sqrt_bound := by
  classical
  intro n G
  have key (s : Finset (Fin n)) (hs : n.sqrt ≤ #s) (ht : G.IsCliqueTransversal sᶜ) :
      G.cliqueTransversalNumber ≤ n - n.sqrt :=
    calc G.cliqueTransversalNumber ≤ #sᶜ := csInf_le' ⟨sᶜ, ht, rfl⟩
      _ ≤ _ := by rw [card_compl, Fintype.card_fin]; omega
  by_cases h : ∃ v, n.sqrt ≤ #(G.neighborFinset v)
  · obtain ⟨v, hv⟩ := h
    refine key _ hv fun t ht => by_contra fun hm => ?_
    simp at hm
    exact G.irrefl (hm v (ht.1.2 (by simpa using ht.1.1.insert fun w hw _ => hm w hw)
      (subset_insert v t) (mem_insert_self v t)))
  · push Not at h
    obtain ⟨s, hs⟩ := G.maximumIndepSet_exists
    have hc : univ ⊆ s.biUnion fun v => insert v (G.neighborFinset v) := fun w _ => by
      by_contra hw
      simp only [mem_biUnion, mem_insert, mem_neighborFinset, not_exists, not_and, not_or] at hw
      exact (hw w ((hs.isMaximalIndepSet s).2 (Set.Pairwise.insert hs.isIndepSet fun v hv _ =>
        ⟨fun h' => (hw v hv).2 h'.symm, (hw v hv).2⟩) (Set.subset_insert w _) (Set.mem_insert w _))).1 rfl
    have hcard : n ≤ #s * n.sqrt := by
      simpa using (card_le_card hc).trans
        (card_biUnion_le_card_mul _ _ _ fun v _ => (card_insert_le v _).trans (h v))
    refine key s (by by_contra! hlt; nlinarith [Nat.sqrt_le n]) fun t ht => ?_
    obtain ⟨a, ha, b, hb, hab⟩ := one_lt_card.mp ht.2
    by_cases hsa : a ∈ s
    · exact ⟨b, hb, mem_compl.mpr fun hsb => hs.isIndepSet hsa hsb hab (ht.1.1 ha hb hab)⟩
    · exact ⟨a, ha, mem_compl.mpr hsa⟩
