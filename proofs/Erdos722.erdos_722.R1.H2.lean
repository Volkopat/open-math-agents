import OMAReductions.R_Erdos722_erdos_722_R1

open Finset

theorem OMA.solution : OMA.R_Erdos722_erdos_722_R1.H2 := by
  classical
  intro n k r hrk
  dsimp only
  rintro ⟨φ, hφ⟩ ⟨a, R, c, u, _, _, haR, ⟨ψ, hψ⟩, absorb, ⟨hu, huc, huCard⟩, hc, hR⟩
  let U (t : ℕ) := (univ : Finset (Fin n)).powersetCard t
  let L := (U r \ a) \ c
  have huU : u ⊆ U k := fun B hB => mem_powersetCard.mpr ⟨subset_univ B, hu B hB⟩
  have count (A : Finset (Fin n)) (hA : A ∈ U r) :
      (∑ B ∈ U k, (if A ⊆ B then (if B ∈ u then (1 : ℤ) else 0) else 0)) =
        if A ∈ c then 1 else 0 := by
    have hAsize := (mem_powersetCard.mp hA).2
    have hf :
        (U k).filter (fun B => A ⊆ B ∧ B ∈ u) =
          u.filter (fun B => A ∈ B.powersetCard r) := by
      ext B
      simp only [mem_filter, mem_powersetCard, hAsize, and_true]
      exact ⟨fun h => ⟨h.2.2, h.2.1⟩, fun h => ⟨huU h.1, h.2, h.1⟩⟩
    simp_rw [← ite_and]
    rw [sum_boole, hf]
    by_cases hAc : A ∈ c
    · rw [if_pos hAc, huCard A hAc]
      rfl
    · have hempty : u.filter (fun B => A ∈ B.powersetCard r) = ∅ :=
        filter_eq_empty_iff.mpr (fun B hB hAB => hAc (huc B hB hAB))
      rw [if_neg hAc, hempty]
      rfl
  have hL :
      ∃ χ : Finset (Fin n) → ℤ, ∀ A ∈ U r,
        (∑ B ∈ U k, if A ⊆ B then χ B else 0) = if A ∈ L then 1 else 0 := by
    refine ⟨fun B => φ B - ψ B - (if B ∈ u then 1 else 0), ?_⟩
    intro A hA
    calc
      _ = (∑ B ∈ U k, if A ⊆ B then φ B else 0) -
            (∑ B ∈ U k, if A ⊆ B then ψ B else 0) -
              (∑ B ∈ U k, if A ⊆ B then (if B ∈ u then (1 : ℤ) else 0) else 0) := by
        rw [← sum_sub_distrib, ← sum_sub_distrib]
        apply sum_congr rfl
        intro B _
        by_cases hAB : A ⊆ B <;> simp [hAB]
      _ = _ := by
        rw [hφ A hA, hψ A hA, count A hA]
        by_cases haa : A ∈ a <;> by_cases hAc : A ∈ c
        · exact False.elim ((mem_sdiff.mp (hc hAc)).2 haa)
        all_goals simp [L, U, (mem_powersetCard.mp hA).2, haa, hAc]
  obtain ⟨b, hb, hba, hbCard⟩ := absorb L hR hL
  refine ⟨u ∪ b, ?_, ?_⟩
  · intro B hB
    rcases mem_union.mp hB with hB | hB
    · exact hu B hB
    · exact hb B hB
  · intro A hAsize
    have hA : A ∈ U r := mem_powersetCard.mpr ⟨subset_univ A, hAsize⟩
    have hsep : A ∈ c → A ∉ a ∪ L := by
      intro hAc hAB
      rcases mem_union.mp hAB with hAa | hAL
      · exact (mem_sdiff.mp (hc hAc)).2 hAa
      · exact (mem_sdiff.mp hAL).2 hAc
    have hone : ((u ∪ b).filter fun B => A ∈ B.powersetCard r).card = 1 := by
      rw [filter_union]
      by_cases hAc : A ∈ c
      · have hempty : b.filter (fun B => A ∈ B.powersetCard r) = ∅ :=
          filter_eq_empty_iff.mpr (fun B hB hAB => hsep hAc (hba B hB hAB))
        rw [hempty, union_empty]
        exact huCard A hAc
      · have hAB : A ∈ a ∪ L := by
          by_cases haa : A ∈ a
          · exact mem_union_left _ haa
          · exact mem_union_right _ (mem_sdiff.mpr ⟨mem_sdiff.mpr ⟨hA, haa⟩, hAc⟩)
        have hempty : u.filter (fun B => A ∈ B.powersetCard r) = ∅ :=
          filter_eq_empty_iff.mpr (fun B hB hAB => hAc (huc B hB hAB))
        rw [hempty, empty_union]
        exact hbCard A hAB
    simpa only [mem_filter, mem_powersetCard, hAsize, and_true] using
      card_eq_one_iff_existsUnique.mp hone