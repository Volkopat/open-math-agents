import OMAStatements.S_oeis_a217447

open OMA.S_oeis_a217447 in
theorem OMA.solution : type_of% @OMA.S_oeis_a217447.main := by
  intro n hn
  obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le' hn
  cases k with
  | zero => decide
  | succ p =>
    simp [a, Finset.sum_range_succ, Nat.factorial_succ]
    ring
