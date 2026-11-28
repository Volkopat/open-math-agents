import FormalConjectures.ErdosProblems.«151»

theorem OMA.solution : type_of% @Erdos151.erdos_151.variants.cliqueFree_three := λ n G hG => by
  have ⟨I, hI⟩ := (Nat.sSup_mem ⟨0, λ _ _ => ⟨∅, by simp, rfl⟩⟩
    ⟨_, λ k hk => let ⟨s, h⟩ := hk G hG; h.2 ▸ s.card_le_univ⟩ :
    Erdos151.H n ∈ _) G hG
  refine Nat.sInf_le ⟨Iᶜ, λ t ⟨⟨c, _⟩, d⟩ => ?_, by simp [I.card_compl, hI.2]; rfl⟩
  simp
  by_contra! h
  have ⟨a, ha, b, hb, hab⟩ := Finset.one_lt_card.1 d
  exact hI.1 (h a ha) (h b hb) hab (c ha hb hab)
