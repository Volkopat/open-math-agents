import OMAStatements.S_oeis_a000382

open OMA.S_oeis_a000382 in
theorem OMA.solution : type_of% @OMA.S_oeis_a000382.main := by
  refine Nat.le_induction rfl fun n h _ => ?_
  obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le' h
  have : a (k + 9) = 2 * a (k + 8) - a (k + 5) := rfl
  grind
