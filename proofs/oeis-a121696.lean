import OMAStatements.S_oeis_a121696
import Mathlib

open OMA.S_oeis_a121696 in
theorem OMA.solution : type_of% @OMA.S_oeis_a121696.main := by
  intro n hn
  obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le' hn
  have T (m : ℕ) : a (m+2) + a (m+1) = (m+1).factorial * (((m+1)/2 : ℕ) + 1) := by
    induction m with
    | zero => simp [a]
    | succ m ih =>
      have e : (((m+1)/2 : ℕ) : ℤ) + ((m+2)/2 : ℕ) = m+1 := by omega
      rw [show a (m+1+2) = _ from a.eq_4 m]
      simp [Nat.factorial_succ, add_assoc] at e ih ⊢
      linear_combination ih + ((m:ℤ)+1) * m.factorial * e
  have t := T k
  simp [a, Nat.factorial_succ] at t ⊢
  linear_combination (-((k:ℤ)+4)*(k+2)) * t
