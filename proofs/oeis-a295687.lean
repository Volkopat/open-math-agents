import OMAStatements.S_oeis_a295687
import Mathlib

open OMA.S_oeis_a295687 in
theorem OMA.solution : type_of% @OMA.S_oeis_a295687.main := by
  intro n hn
  obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le' hn
  induction k with
  | zero => simp [a]
  | succ k ih =>
    have h := ih (by omega)
    simp [a, mul_add, pow_succ] at h ⊢
    constructor <;> linarith
