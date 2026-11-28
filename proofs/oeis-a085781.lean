import OMAStatements.S_oeis_a085781
import Mathlib

open OMA.S_oeis_a085781 in
theorem OMA.solution : type_of% @OMA.S_oeis_a085781.main := by
  have t (j : ℕ) : a j = (j + 1).centralBinom - 2 ^ j := by
    rw [a, Nat.centralBinom, show 2 * (j + 1) = 2 * j + 1 + 1 by omega, Nat.choose_succ_succ (2 * j + 1),
      Nat.choose_symm_half]
    push_cast
    ring
  have h (k : ℕ) : ((k : ℤ) + 1) * (k + 1).centralBinom = 2 * (2 * k + 1) * k.centralBinom := by
    exact_mod_cast Nat.succ_mul_centralBinom_succ k
  intro n hn
  obtain ⟨k, rfl⟩ : ∃ k, n = k + 3 := ⟨n - 3, by omega⟩
  simp only [Nat.reduceSubDiff, Nat.add_sub_cancel, t]
  have h3 := h (k + 3)
  have h2 := h (k + 2)
  have h1 := h (k + 1)
  push_cast at h1 h2 h3 ⊢
  linear_combination h3 - 4 * h2 + 4 * h1
