import OMAStatements.S_oeis_a112703
import Mathlib

theorem OMA.solution : type_of% @OMA.S_oeis_a112703.main := by
  have z (n : ℕ) : ((n : ℤ) + 2) * catalan (n + 1) = 2 * (2 * n + 1) * catalan n := by
    have := Nat.succ_mul_centralBinom_succ n
    rw [← succ_mul_catalan_eq_centralBinom, ← succ_mul_catalan_eq_centralBinom] at this
    exact_mod_cast Nat.eq_of_mul_eq_mul_left n.succ_pos (by ring_nf at this ⊢; linarith)
  intro n hn
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 2 := ⟨n - 2, by omega⟩
  have c := z (m + 1)
  simp only [OMA.S_oeis_a112703.a, show m + 2 - 1 = m + 1 by omega, show m + 2 - 2 = m by omega,
    Finset.sum_range_succ]
  push_cast at *
  linear_combination 9 ^ (m + 2) * c
