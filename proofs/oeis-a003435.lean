import OMAStatements.S_oeis_a003435
import Mathlib

open OMA.S_oeis_a003435 in
theorem OMA.solution : type_of% @OMA.S_oeis_a003435.main := by
  intro n hn
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 5 := ⟨n - 5, by omega⟩
  have r (k : ℕ) := (div_eq_iff (by linarith [k.cast_nonneg (α := ℚ)] : 2 * ((k : ℚ) + 4) - 3 ≠ 0)).1
    (show a (k + 4) = _ by rw [a]).symm
  have h1 := r (m + 1)
  have h2 := r m
  simp only [add_assoc, Nat.reduceAdd, Nat.cast_add, Nat.cast_one] at h1 h2
  rw [show m + 5 - 1 = m + 4 from rfl, show m + 5 - 2 = m + 3 from rfl, show m + 5 - 3 = m + 2 from rfl]
  refine (mul_eq_zero.1 ?_).resolve_left (by linarith [m.cast_nonneg (α := ℚ)] : 2 * ((m : ℚ) + 5) - 3 ≠ 0)
  push_cast
  linear_combination 3 * h2 - h1
