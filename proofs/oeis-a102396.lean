import OMAStatements.S_oeis_a102396
import Mathlib

namespace JacobsthalDigits

open OMA.S_oeis_a102396

/-- The first difference from twice the preceding term alternates between 1 and -1. -/
private theorem next (k : ℕ) :
    J (k + 1) = 2 * J k + 1 - 2 * ((k % 2 : ℕ) : ℤ) := by
  induction k with
  | zero => rfl
  | succ k ih =>
    change J (k + 2) = 2 * J (k + 1) + 1 - 2 * (((k + 1) % 2 : ℕ) : ℤ)
    rw [J]
    have parity : (((k + 1) % 2 : ℕ) : ℤ) = 1 - ((k % 2 : ℕ) : ℤ) := by omega
    rw [parity]
    omega

theorem byWeight (n : ℕ) : a n = J (weight n) := by
  induction n using Nat.binaryRec with
  | zero => rfl
  | bit b n ih =>
    rw [a, Nat.binaryRec_eq b n (Or.inl rfl)]
    change (if b then 2 * a n + 1 - 2 * ((weight n % 2 : ℕ) : ℤ) else a n) =
      J (weight (n.bit b))
    have hw : weight (n.bit b) = (if b then weight n + 1 else weight n) :=
      Nat.binaryRec_eq (motive := fun _ => ℕ) (zero := 0)
        (bit := fun b _ r => if b then r + 1 else r) b n (Or.inl rfl)
    rw [hw]
    change (if b then 2 * a n + 1 - 2 * ((weight n % 2 : ℕ) : ℤ) else a n) =
      J (if b then weight n + 1 else weight n)
    cases b
    · simpa using ih
    · simp only [if_true, ih]
      exact (next _).symm

end JacobsthalDigits

theorem OMA.solution : type_of% @OMA.S_oeis_a102396.main := by
  intro n
  exact ⟨OMA.S_oeis_a102396.weight n, JacobsthalDigits.byWeight n⟩