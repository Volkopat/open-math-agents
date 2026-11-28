import OMAReductions.R_Erdos711_erdos_711_parts_i_R2_H2_R1_H2_R1_H2_R1

/-!
Proof of `OMA.R_Erdos711_erdos_711_parts_i_R2_H2_R1_H2_R1_H2_R1.H1`.
Among the subfamilies of `U` violating Hall's condition pick one, `V`, of minimal size.
Every proper subfamily of `V` satisfies Hall's condition. Deleting one element `d` gives a
subfamily of size `|V| - 1` whose neighbourhood lies inside that of `V`, so the neighbourhood
of `V` has exactly `|V| - 1` elements and deleting `d` does not shrink it.
-/

namespace OMAProof.Erdos711MinimalDeficient

open Finset

theorem minimal_deficient (U : Finset ℕ) (T : ℕ → Finset ℕ) (hU : (U.biUnion T).card < U.card) :
    ∃ V ⊆ U, V.Nonempty ∧ (V.biUnion T).card + 1 = V.card ∧
      (∀ W ⊂ V, W.card ≤ (W.biUnion T).card) ∧
      (∀ d ∈ V, (V.erase d).biUnion T = V.biUnion T) := by
  classical
  set S := U.powerset.filter (fun V => (V.biUnion T).card < V.card) with hS
  have hUS : U ∈ S := by simp [hS, hU]
  obtain ⟨V, hVS, hmin⟩ := S.exists_min_image Finset.card ⟨U, hUS⟩
  simp only [hS, mem_filter, mem_powerset] at hVS hmin
  obtain ⟨hVU, hVlt⟩ := hVS
  have hW : ∀ W ⊂ V, W.card ≤ (W.biUnion T).card := by
    intro W hWV
    by_contra h
    push Not at h
    have := hmin W ⟨(hWV.subset.trans hVU), h⟩
    have := card_lt_card hWV
    omega
  have hne : V.Nonempty := by
    rcases V.eq_empty_or_nonempty with h | h
    · subst h; simp at hVlt
    · exact h
  have hsub : ∀ d ∈ V, (V.erase d).biUnion T ⊆ V.biUnion T :=
    fun d _ => biUnion_subset_biUnion_of_subset_left _ (erase_subset d V)
  have hlow : ∀ d ∈ V, V.card - 1 ≤ ((V.erase d).biUnion T).card := by
    intro d hd
    have := hW (V.erase d) (erase_ssubset hd)
    rwa [card_erase_of_mem hd] at this
  obtain ⟨d0, hd0⟩ := hne
  have hcard : (V.biUnion T).card + 1 = V.card := by
    have h1 := hlow d0 hd0
    have h2 := card_le_card (hsub d0 hd0)
    omega
  refine ⟨V, hVU, ⟨d0, hd0⟩, hcard, hW, ?_⟩
  intro d hd
  apply eq_of_subset_of_card_le (hsub d hd)
  have := hlow d hd
  omega

end OMAProof.Erdos711MinimalDeficient

open OMAProof.Erdos711MinimalDeficient in
theorem OMA.solution : OMA.R_Erdos711_erdos_711_parts_i_R2_H2_R1_H2_R1_H2_R1.H1 :=
  fun U T hU => minimal_deficient U T hU
