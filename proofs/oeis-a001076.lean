import OMAStatements.S_oeis_a001076
import Mathlib

open OMA.S_oeis_a001076

lemma OMA.key (n : ℕ) :
    (2 : ℤ) * (A001076 (n + 1) : ℤ) = (A001076 (n + 2) : ℤ) - (A001077 (n + 1) : ℤ) ∧
    (2 : ℤ) * (A001076 (n + 2) : ℤ) = (A001076 (n + 3) : ℤ) - (A001077 (n + 2) : ℤ) := by
  induction n with
  | zero => decide
  | succ k ih =>
    refine ⟨ih.2, ?_⟩
    have a3 : A001076 (k + 1 + 3) = 4 * A001076 (k + 3) + A001076 (k + 2) := rfl
    have a2 : A001076 (k + 3) = 4 * A001076 (k + 2) + A001076 (k + 1) := rfl
    have b2 : A001077 (k + 1 + 2) = 4 * A001077 (k + 2) + A001077 (k + 1) := rfl
    rw [show k + 1 + 2 = k + 3 by ring, a3]
    rw [show k + 1 + 2 = k + 3 by ring] at b2
    rw [b2]
    have a2' : (A001076 (k + 3) : ℤ) = 4 * A001076 (k + 2) + A001076 (k + 1) := by exact_mod_cast a2
    push_cast
    linear_combination 4 * ih.2 + ih.1 + 2 * a2'

theorem OMA.solution : type_of% @OMA.S_oeis_a001076.main := fun n => (OMA.key n).1
