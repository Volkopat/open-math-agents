import OMAStatements.S_oeis_a025755

theorem OMA.solution : type_of% @OMA.S_oeis_a025755.main := by
  intro n hn
  obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le' hn
  simp [OMA.S_oeis_a025755.a, ascPochhammer_succ_eval, Nat.factorial_succ, pow_succ]
  field_simp
  ring
