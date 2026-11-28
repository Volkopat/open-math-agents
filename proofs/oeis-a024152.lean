import OMAStatements.S_oeis_a024152
theorem OMA.solution : type_of% @OMA.S_oeis_a024152.main := by
  intro n hn
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 14 := ⟨n - 14, by omega⟩
  simp only [OMA.S_oeis_a024152.a, Nat.reduceSubDiff]
  push_cast
  ring
