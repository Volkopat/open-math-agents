import OMAStatements.S_oeis_a126674

theorem OMA.solution : type_of% @OMA.S_oeis_a126674.main := by
  intro n hn
  obtain ⟨m, rfl⟩ := Nat.exists_eq_add_of_le' hn
  simp (disch := decide) only [OMA.S_oeis_a126674.a, Nat.add_sub_assoc, Nat.reduceSub,
    Nat.add_zero, Finset.sum_range_succ, Nat.factorial_succ]
  push_cast
  field_simp
  ring
