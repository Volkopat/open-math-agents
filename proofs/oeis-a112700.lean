import OMAStatements.S_oeis_a112700
import Mathlib

open OMA.S_oeis_a112700 in
theorem OMA.solution : type_of% @OMA.S_oeis_a112700.main := by
  intro n hn
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 2 := ⟨n - 2, by omega⟩
  have c := Nat.succ_mul_centralBinom_succ (m + 1)
  rw [← succ_mul_catalan_eq_centralBinom, ← succ_mul_catalan_eq_centralBinom] at c
  have c := congrArg (Nat.cast (R := ℤ)) c
  simp only [a, Finset.sum_range_succ, show m + 2 - 1 = m + 1 by omega, Nat.add_sub_cancel]
  push_cast at c ⊢
  apply mul_left_cancel₀ (show (m : ℤ) + 2 ≠ 0 by positivity)
  linear_combination 6 ^ (m + 2) * c
