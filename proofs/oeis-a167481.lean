import OMAStatements.S_oeis_a167481
import Mathlib

-- Problem: oeis-a167481
-- Credit: @JamesSlash (the owner of the agent is credited as the solver)

namespace OMA.P167481
open OMA.S_oeis_a167481

lemma step (n : ℕ) : a (n + 1) = -2 * a n + ((2 * (n + 1)).choose (n + 1) : ℤ) := by
  unfold a
  rw [Finset.sum_range_succ, Finset.mul_sum, Nat.sub_self, pow_zero, one_mul]
  congr 1
  apply Finset.sum_congr rfl
  intro k hk
  rw [Finset.mem_range] at hk
  rw [show n + 1 - k = (n - k) + 1 by omega, pow_succ]
  ring

lemma cb (n : ℕ) : ((n + 1 : ℕ) : ℤ) * ((2 * (n + 1)).choose (n + 1) : ℤ) = 2 * (2 * (n : ℤ) + 1) * ((2 * n).choose n : ℤ) := by
  have h := Nat.succ_mul_centralBinom_succ n
  rw [Nat.centralBinom_eq_two_mul_choose, Nat.centralBinom_eq_two_mul_choose] at h
  exact_mod_cast h

theorem sol : type_of% @OMA.S_oeis_a167481.main := by
  intro n hn
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 2 := ⟨n - 2, by omega⟩
  rw [show m + 2 - 1 = m + 1 by omega, show m + 2 - 2 = m by omega, show m + 2 = (m + 1) + 1 by ring,
    step (m + 1), step m]
  have c := cb (m + 1)
  push_cast at c ⊢
  rw [show m + 1 + 1 = m + 2 by ring] at c ⊢
  linear_combination c

end OMA.P167481

theorem OMA.solution : type_of% @OMA.S_oeis_a167481.main := OMA.P167481.sol
