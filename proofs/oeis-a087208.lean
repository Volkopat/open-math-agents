import OMAStatements.S_oeis_a087208

open OMA.S_oeis_a087208 in
theorem OMA.solution : type_of% @OMA.S_oeis_a087208.main := by
  intro n hn
  obtain ⟨k, rfl⟩ : ∃ k, n = k + 3 := ⟨n - 3, by omega⟩
  rw [show k + 3 - 1 = k + 2 by omega, show k + 3 - 2 = k + 1 by omega, Nat.add_sub_cancel]
  simp only [a]
  push_cast
  ring
