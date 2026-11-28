import OMAReductions.R_mo_514705_R1
import Mathlib

-- Credit: @LordMike

theorem OMA.solution : OMA.R_mo_514705_R1.H1 := by
  intro n m 𝓕 x k huc hx hk
  have hnn : ∀ A : Finset (Fin n), 0 ≤ ∑ B ∈ (A.erase k).powersetCard m, ∏ i ∈ B, x i :=
    fun A => Finset.sum_nonneg (fun B _ => Finset.prod_nonneg (fun i _ => hx i))
  have hrhs : ∑ A ∈ 𝓕.filter (fun A => k ∉ A), ∑ B ∈ A.powersetCard m, ∏ i ∈ B, x i
      = ∑ A ∈ 𝓕.filter (fun A => k ∉ A),
          ∑ B ∈ ((insert k A).erase k).powersetCard m, ∏ i ∈ B, x i := by
    apply Finset.sum_congr rfl
    intro A hA
    rw [Finset.mem_filter] at hA
    rw [Finset.erase_insert hA.2]
  have hinj : ∀ A ∈ 𝓕.filter (fun A => k ∉ A), ∀ A' ∈ 𝓕.filter (fun A => k ∉ A),
      insert k A = insert k A' → A = A' := by
    intro A hA A' hA' h
    rw [Finset.mem_filter] at hA hA'
    have h2 := congrArg (fun s => Finset.erase s k) h
    simp only [Finset.erase_insert hA.2, Finset.erase_insert hA'.2] at h2
    exact h2
  have hsub : (𝓕.filter (fun A => k ∉ A)).image (fun A => insert k A)
      ⊆ 𝓕.filter (fun A => k ∈ A) := by
    intro A' hA'
    rw [Finset.mem_image] at hA'
    obtain ⟨A, hA, rfl⟩ := hA'
    rw [Finset.mem_filter] at hA
    rw [Finset.mem_filter]
    refine ⟨?_, Finset.mem_insert_self k A⟩
    show insert k A ∈ 𝓕
    rw [Finset.insert_eq]
    exact huc {k} hk A hA.1
  have hsum_img : ∑ A ∈ (𝓕.filter (fun A => k ∉ A)).image (fun A => insert k A),
        ∑ B ∈ (A.erase k).powersetCard m, ∏ i ∈ B, x i
      = ∑ A ∈ 𝓕.filter (fun A => k ∉ A),
          ∑ B ∈ ((insert k A).erase k).powersetCard m, ∏ i ∈ B, x i := by
    rw [Finset.sum_image (fun A hA A' hA' h => hinj A hA A' hA' h)]
  have hle : ∑ A ∈ (𝓕.filter (fun A => k ∉ A)).image (fun A => insert k A),
        ∑ B ∈ (A.erase k).powersetCard m, ∏ i ∈ B, x i
      ≤ ∑ A ∈ 𝓕.filter (fun A => k ∈ A), ∑ B ∈ (A.erase k).powersetCard m, ∏ i ∈ B, x i :=
    Finset.sum_le_sum_of_subset_of_nonneg hsub (fun A _ _ => hnn A)
  rw [hrhs, ← hsum_img]
  exact hle
