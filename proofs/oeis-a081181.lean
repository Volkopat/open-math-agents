import OMAStatements.S_oeis_a081181
import Mathlib

open OMA.S_oeis_a081181 in
theorem OMA.solution : type_of% @OMA.S_oeis_a081181.main := by
  intro n hn
  obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le' hn
  rw [← Int.cast_inj (α := ℚ)]
  obtain ⟨i, rfl | rfl⟩ := Nat.even_or_odd' k <;>
  simp (disch := omega) [a, show ∀ c, (2*i+c)/2 = i + c/2 by omega, add_assoc, Nat.cast_choose ℚ,
    show ∀ m c, m ≤ c → 3*i + c - (2*i+m) = i + (c - m) by omega,
    show ∀ d, 3*i + d - 2*i = i + d by omega,
    show ∀ c d, i + (c + (2*i+d)) = 3*i + (c+d) by omega,
    show ∀ d, i + (2*i+d) = 3*i + d by omega, Nat.factorial_succ] <;>
  field_simp <;> ring
