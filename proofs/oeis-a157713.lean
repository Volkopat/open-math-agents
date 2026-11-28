import OMAStatements.S_oeis_a157713

open OMA.S_oeis_a157713

theorem OMA.solution : type_of% @OMA.S_oeis_a157713.main := by
  intro n hn
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 2 := ⟨n - 2, by omega⟩
  simp only [a, show m + 2 - 1 = m + 1 from rfl, show m + 1 - 1 = m from rfl,
    show 2 * (m + 2) + 1 = 2 * m + 5 from rfl, show 2 * (m + 2) - 2 = 2 * m + 2 from rfl,
    show 2 * (m + 1) + 1 = 2 * m + 3 from rfl, show 2 * (m + 1) - 2 = 2 * m from rfl,
    Nat.factorial_succ]
  push_cast
  field_simp
  ring
