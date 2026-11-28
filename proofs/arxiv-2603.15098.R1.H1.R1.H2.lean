import OMAReductions.R_arxiv_2603_15098_R1_H1_R1
import Mathlib

/-! Port of the disk-remainder argument in SliceReduction.circle_of_disk_remainder. -/
open Set OMA.S_arxiv_2603_15098

theorem OMA.solution : OMA.R_arxiv_2603_15098_R1_H1_R1.H2 := by
  classical
  intro V M ho hc hd ht
  refine ⟨ho, hc, ?_⟩
  intro p hp
  by_cases h : ∃ i ∈ M, p ∈ connectedComponentIn Vᶜ i
  · obtain ⟨i, him, hi⟩ := h
    exact Or.inr ((connectedComponentIn_eq hi) ▸ hd i him)
  · have hsub : connectedComponentIn Vᶜ p ⊆ Vᶜ \ ⋃ i ∈ M, connectedComponentIn Vᶜ i := by
      intro z hz
      refine ⟨connectedComponentIn_subset _ _ hz, ?_⟩
      intro hu
      obtain ⟨i, him, hi⟩ := mem_iUnion₂.mp hu
      apply h
      refine ⟨i, him, ?_⟩
      rw [connectedComponentIn_eq hi, ← connectedComponentIn_eq hz]
      exact mem_connectedComponentIn hp
    have hs := ht _ hsub isPreconnected_connectedComponentIn
    exact Or.inl ⟨p, Set.Subset.antisymm (fun z hz => Set.mem_singleton_iff.mpr
      (hs hz (mem_connectedComponentIn hp))) (singleton_subset_iff.mpr (mem_connectedComponentIn hp))⟩
