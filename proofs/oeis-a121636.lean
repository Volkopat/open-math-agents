import OMAStatements.S_oeis_a121636

theorem OMA.solution : type_of% @OMA.S_oeis_a121636.main := by
  intro n hn
  obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le' hn
  simp [OMA.S_oeis_a121636.a, Nat.factorial_succ]
  ring
