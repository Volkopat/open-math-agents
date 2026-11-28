import OMAStatements.S_oeis_a193282

theorem OMA.solution : type_of% @OMA.S_oeis_a193282.main := by
  intro n hn
  obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le' hn
  obtain ⟨i, rfl | rfl⟩ := Nat.even_or_odd' k <;>
  simp [OMA.S_oeis_a193282.a, show ∀ c, (2*i+c)/2 = i + c/2 by omega,
    show ∀ c, (2*i+1+c)/2 = i + (c+1)/2 by omega, Nat.factorial_succ] <;>
  field_simp <;> ring
