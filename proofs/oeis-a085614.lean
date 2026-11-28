import OMAStatements.S_oeis_a085614

theorem OMA.solution : type_of% @OMA.S_oeis_a085614.main := by
  intro n hn
  obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le' hn
  simp [OMA.S_oeis_a085614.a, Nat.factorial_succ, pow_succ, mul_add, Nat.doubleFactorial]
  field_simp
  ring
