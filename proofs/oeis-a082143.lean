import OMAStatements.S_oeis_a082143

open OMA.S_oeis_a082143

theorem OMA.solution : type_of% @OMA.S_oeis_a082143.main := by
  intro n hn
  obtain ⟨m, rfl⟩ := Nat.exists_eq_add_of_le' hn
  have h1 := Nat.add_one_mul_choose_eq (2*m+4) (m+1)
  have h2 := Nat.choose_mul_succ_eq (2*m+3) (m+1)
  rw [show 2*m+3+1-(m+1) = m+3 by omega] at h2
  qify at h1 h2
  simp only [a, T, show m+2-1 = m+1 by omega]
  rw [show ((m+2:ℕ):ℤ)-1 = (m+1:ℕ) by omega, show ((m+1:ℕ):ℤ)-1 = m by omega, zpow_natCast, zpow_natCast]
  simp
  refine mul_left_cancel₀ (show (m:ℚ)+2 ≠ 0 by positivity) ?_
  ring_nf at *
  linear_combination 2^m*(-2*(m+3)*h1 - 2*(2*m+5)*h2)
