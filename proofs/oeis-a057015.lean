import OMAStatements.S_oeis_a057015

theorem OMA.solution : type_of% @OMA.S_oeis_a057015.main := by
  rintro k ⟨h1, -, -, h9⟩ hk
  have := h1.eq_one_or_self_of_dvd 2
  have := h1.eq_one_or_self_of_dvd 5
  have := h9.eq_one_or_self_of_dvd 5
  have := Nat.pow_mod k 2 10
  have : 9 ≤ k ^ 2 := by nlinarith
  have := Nat.mod_lt k (show 10 > 0 by norm_num)
  interval_cases h : k % 10 <;> omega
