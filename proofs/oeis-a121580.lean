import OMAStatements.S_oeis_a121580

theorem OMA.solution : type_of% @OMA.S_oeis_a121580.main := by
  intro n hn
  obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le' hn
  simp [OMA.S_oeis_a121580.a, Nat.factorial_succ, pow_succ]
  field_simp
  ring
