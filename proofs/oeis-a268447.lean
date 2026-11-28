import OMAStatements.S_oeis_a268447

theorem OMA.solution : type_of% @OMA.S_oeis_a268447.main := by
  intro n hn
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 9 := ⟨n - 9, by omega⟩
  simp only [OMA.S_oeis_a268447.a, show m + 9 - 1 = m + 8 by omega, show m + 9 - 8 = m + 1 by omega,
    show m + 8 - 8 = m by omega, show 2 * (m + 9) + 1 = 2 * (m + 8) + 1 + 2 by ring,
    Nat.add_assoc, Nat.reduceAdd, Nat.factorial_succ (m + 18), Nat.factorial_succ m,
    Nat.factorial_succ (2 * (m + 8) + 1 + 1), Nat.factorial_succ (2 * (m + 8) + 1)]
  push_cast
  field_simp
  ring
