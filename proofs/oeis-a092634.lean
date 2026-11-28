import OMAStatements.S_oeis_a092634

open OMA.S_oeis_a092634

theorem OMA.solution : type_of% @OMA.S_oeis_a092634.main := by
  intro n hn
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 5 := ⟨n - 5, by omega⟩
  simp [a, Finset.sum_Icc_succ_top, Nat.factorial_succ, show m + 5 - 1 = m + 4 from rfl,
    show m + 5 - 2 = m + 3 from rfl, show m + 5 - 3 = m + 2 from rfl] <;> ring
