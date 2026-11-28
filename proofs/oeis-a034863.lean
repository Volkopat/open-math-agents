import OMAStatements.S_oeis_a034863
import Mathlib

theorem OMA.solution : type_of% @OMA.S_oeis_a034863.main := by
  intro n hn
  obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le' hn
  simp [OMA.S_oeis_a034863.a, Nat.factorial_succ] <;> ring
