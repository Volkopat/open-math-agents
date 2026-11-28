import OMAStatements.S_oeis_a024719

open OMA.S_oeis_a024719 in
theorem OMA.solution : type_of% @OMA.S_oeis_a024719.main := by
  intro n hn
  obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le' hn
  have h : 2*(k+2:ℚ)*(2*k+3) * (3*(k+2)).choose (k+2) = 3*(3*k+5)*(3*k+4) * (3*(k+1)).choose (k+1) := by
    rw [Nat.cast_choose ℚ (by omega), Nat.cast_choose ℚ (by omega), show 3*(k+2)-(k+2) = 2*k+4 by omega, show 3*(k+1)-(k+1)=2*k+2 by omega]
    simp [mul_add, Nat.factorial_succ]
    field_simp
    ring
  simp [a, Finset.sum_range_succ] at h ⊢
  linear_combination h/3
