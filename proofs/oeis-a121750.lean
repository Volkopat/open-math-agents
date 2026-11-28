import OMAStatements.S_oeis_a121750
import Mathlib

set_option maxRecDepth 100000 in
open OMA.S_oeis_a121750 in
theorem OMA.solution : type_of% @OMA.S_oeis_a121750.main := by
  intro n hn
  obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le' hn
  obtain ⟨i, rfl | rfl⟩ := Nat.even_or_odd' k <;> rcases i with _ | j
  · norm_num [a, d, Nat.factorial]
  · simp [a, d, mul_add, add_assoc, show ∀ c, (2*j+c)%2 = c%2 by omega,
      show ∀ c, (2*j+c)/2 = j+c/2 by omega, Nat.factorial_succ]
    ring
  · norm_num [a, d, Nat.factorial]
  · simp [a, d, mul_add, add_assoc, show ∀ c, (2*j+c)%2 = c%2 by omega,
      show ∀ c, (2*j+c)/2 = j+c/2 by omega, Nat.factorial_succ]
    ring
