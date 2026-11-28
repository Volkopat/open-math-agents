import OMAStatements.S_oeis_a005562
import Mathlib

open OMA.S_oeis_a005562 in
theorem OMA.solution : type_of% @OMA.S_oeis_a005562.main := by
  intro n hn
  obtain ⟨i, rfl | rfl | rfl⟩ : ∃ i, n = 6 ∨ n = 2*i+7 ∨ n = 2*i+8 := ⟨(n-7)/2, by omega⟩
  · simp [a, column]
    norm_num
  all_goals
    simp [a, column, add_assoc, show ∀ c, 4+(2*i+c) = 2*i+(c+4) by omega, show ∀ c, (2*i+c)/2 = i+c/2 by omega]
    simp (disch := omega) [Nat.cast_choose, show ∀ c d, 2*i+c-(i+d) = i+c-d by omega, show ∀ c, 2*i+c-i = i+c by omega, Nat.factorial_succ]
    field_simp
    ring
