import OMAStatements.S_oeis_a026021
import Mathlib

open OMA.S_oeis_a026021 in
theorem OMA.solution : type_of% @OMA.S_oeis_a026021.main := by
  intro n hn
  obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le' hn
  obtain ⟨i, rfl | rfl⟩ := Nat.even_or_odd' k <;> obtain h | h := lt_or_ge i 3 <;> first
  | (interval_cases i <;> norm_num [a, T, Nat.choose]; done)
  | (obtain ⟨j, rfl⟩ := Nat.exists_eq_add_of_le' h
     simp (disch := omega) [a, T, mul_add, add_assoc, show ∀ c, (2*j+c)/2 = j+c/2 by omega,
       Nat.cast_choose ℚ, show ∀ m c, m ≤ c → 2*j+c-(j+m) = j+(c-m) by omega,
       show ∀ c, 2*j+c-j = j+c by omega, Nat.factorial_succ]
     field_simp
     ring)
