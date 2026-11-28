import OMAStatements.S_opg_every_metamonovalued_reloid_is_monovalued

open Filter Set
open OMA.S_opg_every_metamonovalued_reloid_is_monovalued

private theorem relComp_mono {A B C : Type} {F F' : Set (A × B)} {G G' : Set (B × C)}
    (hF : F ⊆ F') (hG : G ⊆ G') : relComp F G ⊆ relComp F' G' := by
  rintro p ⟨b, hb, hb'⟩
  exact ⟨b, hF hb, hG hb'⟩

private theorem mem_comp_principal {A B C : Type} (f : Filter (A × B)) (R : Set (B × C))
    (U : Set (A × C)) :
    U ∈ comp (𝓟 R) f ↔ ∃ F ∈ f, relComp F R ⊆ U := by
  have inner (F : Set (A × B)) :
      (⨅ G ∈ 𝓟 R, 𝓟 (relComp F G)) = 𝓟 (relComp F R) := by
    apply le_antisymm
    · exact iInf_le_of_le R (iInf_le _ (mem_principal_self R))
    · refine le_iInf fun G => le_iInf fun hG => principal_mono.mpr ?_
      exact relComp_mono Subset.rfl (mem_principal.mp hG)
  unfold comp
  simp_rw [inner]
  have directed : DirectedOn
      (fun F G : Set (A × B) => 𝓟 (relComp F R) ≥ 𝓟 (relComp G R))
      {F | F ∈ f} := by
    intro F hF G hG
    exact ⟨F ∩ G, inter_mem hF hG,
      principal_mono.mpr (relComp_mono inter_subset_left Subset.rfl),
      principal_mono.mpr (relComp_mono inter_subset_right Subset.rfl)⟩
  simpa only [mem_principal, mem_ofPred_eq] using
    (mem_biInf_of_directed directed ⟨univ, univ_mem⟩ (t := U))

theorem OMA.solution : type_of% @OMA.S_opg_every_metamonovalued_reloid_is_monovalued.main := by
  intro A B f hf
  let left : Set (B × (B × B)) := {p | p.2.1 ≠ p.2.2 ∧ p.1 = p.2.1}
  let right : Set (B × (B × B)) := {p | p.2.1 ≠ p.2.2 ∧ p.1 = p.2.2}
  have hempty : left ∩ right = ∅ := by
    apply eq_empty_iff_forall_notMem.mpr
    rintro p ⟨⟨hne, hleft⟩, _, hright⟩
    exact hne (hleft.symm.trans hright)
  have hbottom : comp (𝓟 (∅ : Set (B × (B × B)))) f = ⊥ := by
    apply empty_mem_iff_bot.mp
    apply (mem_comp_principal f _ _).mpr
    refine ⟨univ, univ_mem, ?_⟩
    rintro p ⟨b, _, hb⟩
    exact hb
  have hmeet := hf (B × B) ({𝓟 left, 𝓟 right} : Set (Filter (B × (B × B))))
  have hpair : (⨅ g ∈ ({𝓟 left, 𝓟 right} : Set (Filter (B × (B × B)))), comp g f) =
      comp (𝓟 left) f ⊓ comp (𝓟 right) f := by
    apply le_antisymm
    · exact le_inf (iInf_le_of_le (𝓟 left) (iInf_le _ (by simp)))
        (iInf_le_of_le (𝓟 right) (iInf_le _ (by simp)))
    · refine le_iInf fun g => le_iInf fun hg => ?_
      simp only [mem_insert_iff, mem_singleton_iff] at hg
      rcases hg with rfl | rfl
      · exact inf_le_left
      · exact inf_le_right
  rw [sInf_pair, inf_principal, hempty, hbottom, hpair] at hmeet
  have hmem : ∅ ∈ comp (𝓟 left) f ⊓ comp (𝓟 right) f := hmeet ▸ mem_bot
  obtain ⟨U, hU, V, hV, hUV⟩ := mem_inf_iff_superset.mp hmem
  obtain ⟨F, hF, hFU⟩ := (mem_comp_principal f left U).mp hU
  obtain ⟨G, hG, hGV⟩ := (mem_comp_principal f right V).mp hV
  have hinv : Prod.swap ⁻¹' (F ∩ G) ∈ inv f := by
    change Prod.swap ⁻¹' (Prod.swap ⁻¹' (F ∩ G)) ∈ f
    have hs : Prod.swap ⁻¹' (Prod.swap ⁻¹' (F ∩ G)) = F ∩ G := by
      ext p
      cases p
      rfl
    rw [hs]
    exact inter_mem hF hG
  unfold Monovalued idRLD comp
  refine iInf_le_of_le (Prod.swap ⁻¹' (F ∩ G)) (iInf_le_of_le hinv ?_)
  refine iInf_le_of_le (F ∩ G) (iInf_le_of_le (inter_mem hF hG) ?_)
  apply principal_mono.mpr
  rintro ⟨b, c⟩ ⟨a, ha, hc⟩
  change (a, b) ∈ F ∩ G at ha
  change b = c
  by_contra hne
  have hleft : (a, (b, c)) ∈ U := hFU ⟨b, ha.1, hne, rfl⟩
  have hright : (a, (b, c)) ∈ V := hGV ⟨c, hc.2, hne, rfl⟩
  exact hUV ⟨hleft, hright⟩
