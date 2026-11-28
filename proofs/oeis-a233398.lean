import OMAStatements.S_oeis_a233398

theorem OMA.solution : type_of% @OMA.S_oeis_a233398.main := by
  rintro x ⟨y, rfl⟩
  simp only [OMA.S_oeis_a233398.a]
  exact Nat.mod_eq_zero_of_dvd ⟨y ^ (3 * y), by rw [mul_pow]⟩
