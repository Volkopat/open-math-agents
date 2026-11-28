import OMAStatements.S_mo_490846
import Mathlib

open Finset

theorem OMA.solution : type_of% @OMA.S_mo_490846.main := by
  classical
  intro n F closed hnonempty y hy
  obtain ⟨A₀, hA₀, hpos⟩ := hnonempty
  let w (A : Finset (Fin n)) : ℝ := ∑ i ∈ A, y i
  obtain ⟨M, hMF, hmax⟩ := exists_max_image F w ⟨A₀, hA₀⟩
  have subMax {A : Finset (Fin n)} (hA : A ∈ F) : A ⊆ M := by
    intro i hi
    by_contra hn
    have hw := sum_lt_sum_of_subset (f := y) (subset_union_left (s₂ := A)) (mem_union_right _ hi)
      hn (hy i) (fun j _ _ => (hy j).le)
    exact (not_lt_of_ge (hmax (M ∪ A) (closed M hMF A hA))) hw
  let left (k : Fin n) (s : ℝ) := F.filter fun A => k ∈ A ∧ w A = s
  let right (k : Fin n) (s : ℝ) := F.filter fun A => k ∉ A ∧ w (insert k A) = s
  change ∃ k, (∀ s, (left k s).card = (right k s).card) ∨
    ∃ s, (right k s).card < (left k s).card ∧
      ∀ t, s < t → (left k t).card = (right k t).card
  have pairCard (k : Fin n) (s : ℝ) :
      ((right k s).image (insert k)).card = (right k s).card := by
    apply card_image_of_injOn
    intro A hA B hB h
    have hAk := (mem_filter.mp hA).2.1
    have hBk := (mem_filter.mp hB).2.1
    simpa only [erase_insert hAk, erase_insert hBk] using congrArg (fun C => C.erase k) h
  have pairSub (k : Fin n) (s : ℝ)
      (h : ∀ A ∈ right k s, insert k A ∈ F) :
      (right k s).image (insert k) ⊆ left k s := by
    intro C hC
    obtain ⟨A, hA, rfl⟩ := mem_image.mp hC
    exact mem_filter.mpr ⟨h A hA, mem_insert_self _ _, (mem_filter.mp hA).2.2⟩
  by_cases hholes : ∃ B : Finset (Fin n), B ⊆ M ∧ B ∉ F
  · let holes := M.powerset \ F
    obtain ⟨B, hB⟩ := hholes
    obtain ⟨D, hD, hmaxD⟩ := exists_max_image holes w
      ⟨B, mem_sdiff.mpr ⟨mem_powerset.mpr hB.1, hB.2⟩⟩
    have hDM : D ⊆ M := mem_powerset.mp (mem_sdiff.mp hD).1
    have hDF : D ∉ F := (mem_sdiff.mp hD).2
    have proper := (Finset.ssubset_iff_subset_ne (s := D) (t := M)).mpr
      ⟨hDM, fun h => hDF (h.symm ▸ hMF)⟩
    obtain ⟨k, hk, hkD⟩ := (ssubset_iff_of_subset hDM).mp proper
    have above {A : Finset (Fin n)} (hA : A ⊆ M) (h : w D < w A) : A ∈ F := by
      by_contra hn
      exact (not_lt_of_ge (hmaxD A (mem_sdiff.mpr ⟨mem_powerset.mpr hA, hn⟩))) h
    have pairs (s : ℝ) (hs : w D < s) :
        (right k s).image (insert k) ⊆ left k s := by
      apply pairSub
      intro A hA
      have p := mem_filter.mp hA
      exact above (insert_subset_iff.mpr ⟨hk, subMax p.1⟩) (p.2.2.symm ▸ hs)
    let s₀ := w (insert k D)
    have hless : w D < s₀ := by
      dsimp only [s₀, w]
      rw [sum_insert hkD]
      linarith [hy k]
    have hDins : insert k D ∈ F := above (insert_subset_iff.mpr ⟨hk, hDM⟩) hless
    have strict₀ : (right k s₀).card < (left k s₀).card := by
      rw [← pairCard]
      apply card_lt_card
      apply (ssubset_iff_of_subset (pairs s₀ hless)).mpr
      refine ⟨insert k D, mem_filter.mpr ⟨hDins, mem_insert_self _ _, rfl⟩, ?_⟩
      intro ha
      obtain ⟨A, hA, he⟩ := mem_image.mp ha
      have hp := mem_filter.mp hA
      have hAD : A = D := by
        simpa only [erase_insert hp.2.1, erase_insert hkD] using congrArg (fun C => C.erase k) he
      exact hDF (hAD ▸ hp.1)
    let good := (F.image w).filter fun s => (right k s).card < (left k s).card
    have hs₀ : s₀ ∈ good := mem_filter.mpr ⟨mem_image_of_mem w hDins, strict₀⟩
    obtain ⟨s, hs, hmaxS⟩ := exists_max_image good id ⟨s₀, hs₀⟩
    refine ⟨k, Or.inr ⟨s, (mem_filter.mp hs).2, ?_⟩⟩
    intro t ht
    have hDt : w D < t := hless.trans ((hmaxS s₀ hs₀).trans_lt ht)
    have hle : (right k t).card ≤ (left k t).card := by
      rw [← pairCard]
      exact card_le_card (pairs t hDt)
    apply le_antisymm _ hle
    by_contra! hlt
    have cardpos : 0 < (left k t).card := (Nat.zero_le _).trans_lt hlt
    obtain ⟨A, hA⟩ := card_pos.mp cardpos
    have p := mem_filter.mp hA
    have ht' : t ∈ good := mem_filter.mpr ⟨mem_image.mpr ⟨A, p.1, p.2.2⟩, hlt⟩
    exact (not_lt_of_ge (hmaxS t ht')) ht
  · have full {B : Finset (Fin n)} (hB : B ⊆ M) : B ∈ F := by
      by_contra h
      exact hholes ⟨B, hB, h⟩
    obtain ⟨k, hk⟩ := hpos.mono (subMax hA₀)
    refine ⟨k, Or.inl ?_⟩
    intro s
    rw [← pairCard]
    congr 1
    apply Subset.antisymm
    · intro A hA
      have p := mem_filter.mp hA
      exact mem_image.mpr ⟨A.erase k, mem_filter.mpr ⟨
        full ((erase_subset _ _).trans (subMax p.1)), notMem_erase _ _, by rw [insert_erase p.2.1]; exact p.2.2⟩,
        insert_erase p.2.1⟩
    · apply pairSub
      intro A hA
      exact full (insert_subset_iff.mpr ⟨hk, subMax (mem_filter.mp hA).1⟩)