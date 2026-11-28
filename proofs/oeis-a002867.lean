import OMAStatements.S_oeis_a002867
import Mathlib

open OMA.S_oeis_a002867 in
theorem OMA.solution : type_of% @OMA.S_oeis_a002867.main := by
  intro n hn
  obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le' hn
  rw [← Int.cast_inj (α := ℚ)]
  obtain ⟨i, rfl | rfl⟩ := Nat.even_or_odd' k <;>
  simp (disch := omega) [a, add_assoc, show ∀ c, (2*i+c)/2 = i+c/2 by omega,
    Nat.cast_choose ℚ, show ∀ m c, m ≤ c → 2*i+c-(i+m) = i+(c-m) by omega,
    show ∀ c, 2*i+c-i = i+c by omega, show 2*i-i = i by omega, Nat.factorial_succ] <;>
  field_simp <;> ring
