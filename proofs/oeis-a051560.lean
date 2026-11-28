import OMAStatements.S_oeis_a051560
import Mathlib

open OMA.S_oeis_a051560 in
theorem OMA.solution : type_of% @OMA.S_oeis_a051560.main := by
  have h (n : ℕ) : 0 ≤ (-1) ^ n * T n 0 ∧ 0 ≤ (-1) ^ (n + 1) * T n 1 := by
    induction n with
    | zero => simp [T]
    | succ n ih =>
      have := Nat.cast_nonneg (α := ℤ) (n + 1 + 7)
      simp only [T, pow_succ] at *
      constructor <;> nlinarith [mul_nonneg this ih.1, mul_nonneg this ih.2]
  have e (n : ℕ) : a n = (-1) ^ (n + 1) * T n 1 := by
    rw [a, ← abs_of_nonneg (h n).2]
    simp [abs_mul]
  intro n
  simp only [e, T, pow_succ]
  push_cast
  ring
