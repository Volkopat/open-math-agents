import OMAStatements.S_oeis_a372991
import Mathlib

open OMA.S_oeis_a372991 in
theorem OMA.solution : type_of% @OMA.S_oeis_a372991.main := by
  intro n hn
  obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le' hn
  have p : ∀ n, 0 < a n ∧ 0 < a (n+1) := by
    intro n
    induction n with
    | zero => simp [a]
    | succ n ih => exact ⟨ih.2, by rw [a]; exact div_pos (by positivity) (mul_pos ih.2 ih.1)⟩
  have h1 := (p k).1
  have h2 := (p k).2
  simp [a, mul_add, Nat.factorial_succ]
  field_simp
  ring
