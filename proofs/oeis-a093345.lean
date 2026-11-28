import OMAStatements.S_oeis_a093345
import Mathlib

theorem OMA.solution : type_of% @OMA.S_oeis_a093345.main := by
  intro n hn
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 3 := ⟨n - 3, by omega⟩
  simp only [OMA.S_oeis_a093345.a, Nat.reduceSubDiff, Finset.sum_Icc_succ_top (Nat.le_add_left 1 _),
    Finset.sum_range_succ, Nat.factorial_succ]
  push_cast
  field_simp
  ring
