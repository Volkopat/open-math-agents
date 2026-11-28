import OMAReductions.R_Erdos615_erdos_615_variants_fox_loh_zhao_R1

-- Step Erdos615.erdos_615.variants.fox_loh_zhao.R1.H2: hypothesis H2 of reduction Erdos615.erdos_615.variants.fox_loh_zhao.R1
-- Credit: @JamesSlash. Pad G with n - m isolated vertices (G' = G.map of the embedding Fin m -> Fin n). G' is still
-- K4-free and has the same edges; an independent set of G' meets the image of Fin m in an independent set of G and
-- has at most n - m further vertices.

theorem OMA.solution : OMA.R_Erdos615_erdos_615_variants_fox_loh_zhao_R1.H2 := by
  intro m G hG n hmn
  classical
  let f : Fin m ↪ Fin n := Fin.castLEEmb hmn
  refine ⟨G.map f, ?_, ?_, ?_⟩
  · rcases Nat.eq_zero_or_pos m with hm | hm
    · subst hm
      have hbot : G.map f = ⊥ := by
        ext u v
        simp only [SimpleGraph.map_adj, SimpleGraph.bot_adj, iff_false]
        rintro ⟨a, -, -⟩
        exact a.elim0
      rw [hbot]
      exact SimpleGraph.cliqueFree_bot (by norm_num)
    · have : Nonempty (Fin m) := ⟨⟨0, hm⟩⟩
      exact SimpleGraph.cliqueFree_map_iff.mpr hG
  · obtain ⟨s, hs⟩ := (G.map f).exists_isNIndepSet_indepNum
    rw [← hs.card_eq]
    have hsplit := Finset.card_filter_add_card_filter_not (s := s) (fun v => v ∈ Set.range f)
    have h1 : (s.filter (fun v => v ∈ Set.range f)).card ≤ G.indepNum := by
      have ht_indep : G.IsIndepSet ((s.preimage f f.injective.injOn : Finset (Fin m)) : Set (Fin m)) := by
        intro u hu v hv huv hadj
        have hu' : f u ∈ (s : Set (Fin n)) := by simpa using hu
        have hv' : f v ∈ (s : Set (Fin n)) := by simpa using hv
        exact hs.isIndepSet hu' hv' (f.injective.ne huv) (SimpleGraph.map_adj_apply.mpr hadj)
      have heq : s.filter (fun v => v ∈ Set.range f) = (s.preimage f f.injective.injOn).map f := by
        ext w
        simp only [Finset.mem_filter, Set.mem_range, Finset.mem_map, Finset.mem_preimage]
        constructor
        · rintro ⟨hw, a, rfl⟩
          exact ⟨a, hw, rfl⟩
        · rintro ⟨a, ha, rfl⟩
          exact ⟨ha, a, rfl⟩
      rw [heq, Finset.card_map]
      exact ht_indep.card_le_indepNum
    have h2 : (s.filter (fun v => v ∉ Set.range f)).card ≤ n - m := by
      have hsub : s.filter (fun v => v ∉ Set.range f) ⊆ (Finset.univ.map f)ᶜ := by
        intro w hw
        simp only [Finset.mem_filter] at hw
        simp only [Finset.mem_compl, Finset.mem_map, Finset.mem_univ, true_and]
        rintro ⟨a, rfl⟩
        exact hw.2 ⟨a, rfl⟩
      calc (s.filter (fun v => v ∉ Set.range f)).card ≤ ((Finset.univ.map f)ᶜ).card :=
            Finset.card_le_card hsub
        _ = n - m := by
            rw [Finset.card_compl, Finset.card_map, Finset.card_univ, Fintype.card_fin, Fintype.card_fin]
    omega
  · rw [SimpleGraph.edgeSet_map, Set.ncard_image_of_injective _ f.sym2Map.injective]
