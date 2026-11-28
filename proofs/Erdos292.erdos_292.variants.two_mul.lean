import FormalConjectures.ErdosProblems.«292»

/-! Doubling the denominators and adding 1/2 preserves a sum of one. -/

open Finset
theorem OMA.solution : type_of% @Erdos292.erdos_292.variants.two_mul := by
  rintro n ⟨S, hS, hn, hs⟩ h
  have h1 : 1 ∉ S := by
    intro h1
    have := single_lt_sum (f := fun k : ℕ => (1 : ℚ) / k)
      (by omega : n ≠ 1) h1 hn (by positivity) (by intros; positivity)
    norm_num only [div_one, hs] at this
  refine ⟨insert 2 (S.image (2 * ·)), fun m hm => ?_, by simp [hn], ?_⟩
  · simp only [mem_insert, mem_image] at hm
    obtain rfl | ⟨k, hk, rfl⟩ := hm
    · simp; omega
    · have := mem_Icc.1 (hS hk)
      simp; omega
  · rw [sum_insert (by simpa using h1), sum_image (by simp)]
    simp at hs ⊢
    rw [← sum_mul, hs]
    norm_num
