import OMAStatements.S_oeis_a124753
import Mathlib

open OMA.S_oeis_a124753 in
theorem OMA.solution : type_of% @OMA.S_oeis_a124753.main := by
  intro n hn
  have c (N : ℕ) : a N = ((N%3:ℕ)+1) * ((4*(N/3)+N%3).factorial / ((N/3).factorial * (3*(N/3)+N%3).factorial)) / (3*(N/3:ℕ)+(N%3:ℕ)+1) := by
    rw [a, Nat.cast_choose ℚ (by omega), show 4*(N/3)+N%3-N/3 = 3*(N/3)+N%3 by omega]
  obtain ⟨i, rfl | rfl | rfl⟩ : ∃ i, n = 3*i+6 ∨ n = 3*i+7 ∨ n = 3*i+8 := ⟨(n-6)/3, by omega⟩ <;>
  · simp only [c]
    simp [show ∀ c, (3*i+c)/3 = i+c/3 by omega, show ∀ c, (3*i+c)%3 = c%3 by omega, mul_add, Nat.factorial_succ]
    field_simp
    ring
