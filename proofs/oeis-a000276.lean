import OMAStatements.S_oeis_a000276
import Mathlib

open OMA.S_oeis_a000276 in
theorem OMA.solution : type_of% @OMA.S_oeis_a000276.main := by
  constructor <;> intro n hn <;> obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le' hn <;>
  simp [a, Nat.factorial_succ, harmonic_succ] <;> field_simp <;> ring
