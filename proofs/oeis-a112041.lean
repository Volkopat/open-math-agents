import OMAStatements.S_oeis_a112041
import Mathlib

theorem OMA.solution : type_of% @OMA.S_oeis_a112041.main := by
  rintro k ⟨h1, h3, h9, h27⟩ hk
  have := h1.eq_one_or_self_of_dvd 2
  have := h1.eq_one_or_self_of_dvd 5
  have := h3.eq_one_or_self_of_dvd 5
  have := h9.eq_one_or_self_of_dvd 5
  have := h27.eq_one_or_self_of_dvd 5
  have : k ≠ 1 := by rintro rfl; norm_num at h3
  have := Nat.mod_lt k (show 10 > 0 by norm_num)
  interval_cases h : k % 10 <;> omega
