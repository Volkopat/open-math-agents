import OMAStatements.S_oeis_a116637

open OMA.S_oeis_a116637 in
theorem OMA.solution : type_of% @OMA.S_oeis_a116637.main := by
  intro n hn
  obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le' hn
  obtain ⟨i, rfl | rfl⟩ := Nat.even_or_odd' k <;>
  simp [a, add_assoc, mul_add, Nat.factorial_succ, show ∀ c, (2*i+c)/2 = i + c/2 by omega, show ∀ c, (2*i+c)%2 = c%2 by omega] <;>
  field_simp <;> ring
