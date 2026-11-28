import OMAStatements.S_oeis_a052227

open OMA.S_oeis_a052227 in
theorem OMA.solution : type_of% @OMA.S_oeis_a052227.main := by
  intro n hn
  obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le' hn
  have c (j : ℕ) : ((3*j).choose j : ℚ) = (3*j).factorial / (j.factorial * (2*j).factorial) := by
    rw [Nat.cast_choose ℚ (by omega), show 3*j-j = 2*j by omega]
  simp only [a, c]
  simp [mul_add, Nat.factorial_succ]
  field_simp
  ring
