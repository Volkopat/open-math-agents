import FormalConjectures.ErdosProblems.«292»

/-! Double the denominators and adjoin `2`. -/

open Finset in
theorem OMA.solution : type_of% @Erdos292.erdos_292.variants.two_mul := by
  rintro n ⟨S, hS, hn, hs⟩ h
  have h1 : 1 ∉ S := fun c => by
    have := single_lt_sum (f := fun k : ℕ => (1 : ℚ) / k) h.ne' c hn (by positivity)
      fun _ _ _ => by positivity
    simp at hs; simp [hs] at this
  refine ⟨insert 2 (S.image (2 * ·)), fun m hm => ?_, by simp [hn], ?_⟩
  · simp at hm ⊢
    obtain rfl | ⟨k, hk, rfl⟩ := hm
    · omega
    · have := mem_Icc.1 (hS hk); omega
  · rw [sum_insert (by simpa using h1), sum_image (by simp)]
    simp at hs ⊢; rw [← sum_mul, hs]; norm_num
