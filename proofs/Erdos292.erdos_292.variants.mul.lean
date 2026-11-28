import FormalConjectures.ErdosProblems.«292»

open Finset

theorem OMA.solution : type_of% @Erdos292.erdos_292.variants.mul := by
  rintro m ⟨S, hS, hm, h⟩ n ⟨T, hT, hn, k⟩
  have mpos := (mem_Icc.mp (hS hm)).1
  let f : ℕ ↪ ℕ := ⟨(m * ·), mul_right_injective₀ (by omega)⟩
  have below {a} (ha : a ∈ S.erase m) : 1 ≤ a ∧ a < m := by
    rw [mem_erase] at ha
    have := mem_Icc.mp (hS ha.2)
    omega
  have above {b} (hb : b ∈ T) : m ≤ f b ∧ f b ≤ m * n := by
    obtain ⟨lo, hi⟩ := mem_Icc.mp (hT hb)
    exact ⟨Nat.le_mul_of_pos_right m lo, Nat.mul_le_mul_left m hi⟩
  have hd : Disjoint (S.erase m) (T.map f) := by
    simp only [disjoint_left, mem_map]
    rintro a ha ⟨b, hb, rfl⟩
    exact (below ha).2.not_ge (above hb).1
  refine ⟨S.erase m ∪ T.map f, ?_, mem_union_right _ (mem_map_of_mem f hn), ?_⟩
  · simp only [Finset.subset_iff, mem_union, mem_map, mem_Icc]
    rintro a (ha | ⟨b, hb, rfl⟩)
    · have := below ha
      have := above hn
      omega
    · have := above hb
      omega
  · rw [sum_union hd, sum_map, sum_erase_eq_sub hm, h]
    simp [f, one_div, ← sum_mul] at k ⊢
    rw [k]
    ring
