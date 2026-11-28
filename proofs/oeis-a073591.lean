import OMAStatements.S_oeis_a073591
import Mathlib

namespace A073591Aux

open OMA.S_oeis_a073591 in
lemma b_succ (n : ℕ) : A000522 (n + 1) = (n + 1) * A000522 n + 1 := by
  unfold A000522
  rw [Finset.sum_range_succ, Nat.div_self (Nat.factorial_pos _), Finset.mul_sum]
  congr 1
  apply Finset.sum_congr rfl
  intro k hk
  have hk' : k ≤ n := by
    have := Finset.mem_range.mp hk
    omega
  rw [Nat.factorial_succ, Nat.mul_div_assoc _ (Nat.factorial_dvd_factorial hk')]

end A073591Aux

open OMA.S_oeis_a073591 in
theorem OMA.solution : type_of% @OMA.S_oeis_a073591.main := by
  intro n hn
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 3 := ⟨n - 3, by omega⟩
  have h1 : A000522 (m + 1) = (m + 1) * A000522 m + 1 := A073591Aux.b_succ m
  have h2 : A000522 (m + 2) = (m + 2) * A000522 (m + 1) + 1 := A073591Aux.b_succ (m + 1)
  have h3 : A000522 (m + 3) = (m + 3) * A000522 (m + 2) + 1 := A073591Aux.b_succ (m + 2)
  have e1 : (A000522 (m + 1) : ℤ) = ((m : ℤ) + 1) * A000522 m + 1 := by exact_mod_cast h1
  have e2 : (A000522 (m + 2) : ℤ) = ((m : ℤ) + 2) * A000522 (m + 1) + 1 := by exact_mod_cast h2
  have e3 : (A000522 (m + 3) : ℤ) = ((m : ℤ) + 3) * A000522 (m + 2) + 1 := by exact_mod_cast h3
  simp only [OMA.S_oeis_a073591.a, show m + 3 - 1 = m + 2 by omega,
    show m + 3 - 2 = m + 1 by omega, show m + 3 - 3 = m by omega]
  push_cast
  linear_combination e3 - 2 * e2 + e1
